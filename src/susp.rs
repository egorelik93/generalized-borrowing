use std::{
    cell::UnsafeCell,
    marker::{PhantomData, PhantomPinned},
    mem::{self, ManuallyDrop, MaybeUninit},
    pin::Pin,
    ptr::{self, NonNull},
};

use crate::{
    inout::InBox,
    mutref::{InternalOutFn, OutFnInput},
    Mut, Typestate,
};

pub struct SuspCell<S, B, A, T = B, F = ()> {
    val: MaybeUninit<Typestate<A, B>>,
    inner: SuspCellShared<S, T, B, F>,
}

pub struct SuspCellTransformer<'m, 'l, S, T, B, F> {
    start: &'l UnsafeCell<dyn DynSuspCellInner<'l, S> + 'l>,
    prev: Option<&'m UnsafeCell<dyn DynTypedSuspCellTransform<'l, S, T, B, F> + 'l>>,
    result: Result<T, State>,
}

pub type SuspCellRef<'l, A, B> = Mut<'l, A, B>;

pub struct SuspCellTransformShared<'l, S, T, B, F>(UnsafeCell<SuspCellTransform<'l, S, T, B, F>>);

/// Will most likely need to be inside a block,
/// in order to force the pin to be dropped before SuspCell is reclaimed.
#[macro_export]
macro_rules! defer {
    ($transformer:ident $(: $type:ty)? = $body:expr;) => {
        let p = core::pin::pin!($transformer.transform$(::<$type, _>)?(|$transformer| $body));
        let $transformer = p.continue_with();
    };
}

struct SuspCellShared<S, T, B, F>(UnsafeCell<SuspCellInner<S, T, B, F>>);

struct SuspCellInner<S, T, B, F> {
    target: Result<S, State>,
    transform: UnsafeCell<SuspCellInitialTransform<S, T, B, F>>,
}

#[derive(Clone, Copy, Eq, Debug, Hash, PartialEq)]
enum State {
    Unfilled,
    Released,
}

trait DynSuspCellInner<'l, S> {
    fn get_transform_mut<'m>(&'m mut self) -> &'m mut dyn DynSuspCellTransform<'l, S>
    where
        'l: 'm;
    fn get_target_mut(&mut self) -> &mut Result<S, State>;
}

/// The 'static lifetimes are fake; the actual lifetime will be that of the borrow.
struct SuspCellInitialTransform<S, T, B, F> {
    // Not storing start eliminates most of the lifetime transmutes we need
    needs_more: bool,
    next_is_boxed: bool,
    next: Option<NonNull<dyn DynSuspCellTransform<'static, S>>>,
    result: Result<T, State>,
    f: Option<F>,
    _phantom_f: PhantomData<dyn FnOnce(B) -> T>,
    _phantom_pinned: PhantomPinned,
}

struct SuspCellTransform<'l, S, T, B, F> {
    start: &'l UnsafeCell<dyn DynSuspCellInner<'l, S> + 'l>,
    needs_more: bool,
    boxed: bool,
    next_is_boxed: bool,
    next: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>,
    prev: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>,
    result: Result<T, State>,
    f: Option<F>,
    _phantom_f: PhantomData<dyn FnOnce(B) -> T>,
    _phantom_pinned: PhantomPinned,
}

trait DynSuspCellTransform<'l, S> {
    fn next(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>;
    // Allowing because having set_prev without prev is bad design.
    #[allow(dead_code)]
    fn prev(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>;
    unsafe fn transform(&mut self, src: *mut ());
    fn get_result(&mut self) -> *mut ();
    // Do not drop the result.
    fn release_result(&mut self);
    fn is_transformed(&self) -> bool;
    fn needs_more(&self) -> bool;
    fn next_is_boxed(&self) -> bool;

    /// move_to_box does not set next and prev, as that would require recursion.
    /// Use the corresponding functions to do that.
    fn move_to_box(&mut self) -> Box<dyn DynSuspCellTransform<'l, S> + 'l>;
    fn set_next_is_boxed(&mut self, is_boxed: bool);
    fn set_next(&mut self, next: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>);
    fn set_prev(&mut self, prev: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>);
}

/// Abstracts over SuspCell(Initial)Transform
trait DynTypedSuspCellTransform<'l, S, T, B, F>: DynSuspCellTransform<'l, S> {
    fn needs_more_mut(&mut self) -> &mut bool;
    fn is_boxed(&self) -> bool;
    fn next_is_boxed_mut(&mut self) -> &mut bool;
    fn result_mut(&mut self) -> &mut Result<T, State>;
    fn f_mut(&mut self) -> &mut Option<F>;
}

impl<S, A, B> SuspCell<S, B, A> {
    pub fn new(a: A) -> Self {
        SuspCell {
            val: MaybeUninit::new(Typestate {
                current: ManuallyDrop::new(a),
            }),
            inner: SuspCellShared(UnsafeCell::new(SuspCellInner {
                transform: UnsafeCell::new(SuspCellInitialTransform::initial(())),
                target: Err(State::Unfilled),
            })),
        }
    }
}

impl<F, S, T, A, B> SuspCell<S, B, A, T, F>
where
    F: FnOnce(B) -> T,
{
    pub fn new_with(a: A, f: F) -> Self {
        SuspCell {
            val: MaybeUninit::new(Typestate {
                current: ManuallyDrop::new(a),
            }),
            inner: SuspCellShared(UnsafeCell::new(SuspCellInner {
                transform: UnsafeCell::new(SuspCellInitialTransform::initial(f)),
                target: Err(State::Unfilled),
            })),
        }
    }
}

#[allow(private_bounds)]
impl<F, S, A, B> SuspCell<S, B, A, S, F>
where
    F: Continuation<B, S>,
{
    pub fn borrow_mut<'l>(&'l mut self) -> SuspCellRef<'l, A, B> {
        assert_eq!(
            self.inner.0.get_mut().target.as_ref().err(),
            Some(&State::Unfilled),
            "Cell was already borrowed"
        );

        let transform = unsafe { (&mut *self.inner.0.get()).transform.get_mut() };
        transform.needs_more = false;

        unsafe { Mut::from_raw_parts(self.val.assume_init_mut(), self.inner.0.get()) }
    }
}

#[allow(private_bounds)]
impl<F, S, T, A, B> SuspCell<S, B, A, T, F>
where
    F: Continuation<B, T>,
{
    pub fn borrow_and_transform<'l>(
        &'l mut self,
    ) -> (
        SuspCellTransformer<'l, 'l, S, T, B, F>,
        SuspCellRef<'l, A, B>,
    ) {
        assert_eq!(
            self.inner.0.get_mut().target.as_ref().err(),
            Some(&State::Unfilled),
            "Cell was already borrowed"
        );

        let m = unsafe { Mut::from_raw_parts(self.val.assume_init_mut(), self.inner.0.get()) };

        let start: &'l UnsafeCell<dyn DynSuspCellInner<'l, S> + 'l> = &self.inner.0;
        let transform = unsafe { &(&*self.inner.0.get()).transform };

        // Cannot use continue_with, as it assumes .prev exists
        let transformer: SuspCellTransformer<'l, 'l, S, T, B, F> = SuspCellTransformer {
            start,
            prev: Some(transform),
            result: Err(State::Unfilled),
        };

        (transformer, m)
    }

    pub fn into_inner(mut self) -> S {
        let target = &mut self.inner.0.get_mut().target;
        if let Ok(result) = mem::replace(target, Err(State::Released)) {
            result
        } else {
            panic!("Mut was never written or transformed")
        }
    }
}

impl<S, T, A, B, F> Drop for SuspCell<S, B, A, T, F> {
    fn drop(&mut self) {
        assert_ne!(
            self.inner.0.get_mut().target.as_ref().err(),
            Some(&State::Unfilled),
            "Mut was not written to or transformed as specified"
        );
    }
}

#[allow(private_bounds)]
impl<'m, 'l, S, B, F> SuspCellTransformer<'m, 'l, S, S, B, F>
where
    F: Continuation<B, S> + 'l,
    S: 'l,
    B: 'l,
{
    /// Preferably call this *after* the corresponding Mutate is released.
    ///
    /// Ideally, this gets called immediately before extracting from the cell.
    /// Otherwise, we will need to allocate memory.
    pub fn release(mut self) {
        let s = &mut self;

        let start = unsafe { &mut *s.start.get() };
        if let Some(result) = take_result(&mut s.result) {
            *start.get_target_mut() = Ok(result);
            return;
        }

        unsafe { s.get_prev_mut().map(|p| *p.needs_more_mut() = false) };

        let initial_transform = start.get_transform_mut();
        if !initial_transform.is_transformed() {
            let mut prev = initial_transform;
            let mut node = prev.next();

            while let Some(mut n) = node {
                let n = unsafe { n.as_mut() };

                node = n.next();

                if !prev.next_is_boxed() {
                    let mut b = n.move_to_box();
                    b.set_prev(Some(unsafe { NonNull::new_unchecked(prev) }));
                    let mut b_raw = unsafe { NonNull::new_unchecked(Box::into_raw(b)) };
                    prev.set_next(Some(b_raw));
                    prev.set_next_is_boxed(true);

                    prev = unsafe { b_raw.as_mut() };
                } else {
                    prev = n
                }
            }
        }
    }
}

#[allow(private_bounds)]
impl<'l, 'm, S, T, B, F> SuspCellTransformer<'m, 'l, S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    pub fn continue_with<U, G>(self, func: G) -> SuspCellTransformer<'static, 'l, S, U, T, G>
    where
        G: FnOnce(T) -> U,
    {
        let mut transform = self.transform(func);
        if let Some(result) = take_result(&mut transform.0.get_mut().result) {
            SuspCellTransformer {
                start: transform.0.get_mut().start,
                prev: None,
                result: Ok(result),
            }
        } else {
            transform.0.get_mut().boxed = true;

            let boxed = Box::new(transform);
            unsafe {
                Pin::new_unchecked(Box::leak(boxed) as &mut SuspCellTransformShared<'l, S, U, T, G>)
            }
            .continue_with()
        }
    }

    pub fn transform<U, G>(mut self, func: G) -> SuspCellTransformShared<'l, S, U, T, G>
    where
        G: FnOnce(T) -> U,
    {
        let result;
        let f;

        if let Some(t) = take_result(&mut self.result) {
            result = Ok(func(t));
            f = None;
        } else if let Some(prev_result) =
            unsafe { take_result(self.get_prev_mut().unwrap().result_mut()) }
        {
            result = Ok(func(prev_result));
            f = None;
        } else {
            result = Err(State::Unfilled);
            f = Some(func);
        }

        SuspCellTransformShared(UnsafeCell::new(SuspCellTransform {
            start: self.start,
            needs_more: true,
            boxed: false,
            next_is_boxed: false,
            next: None,
            prev: unsafe {
                self.get_prev_mut()
                    .map(|p| NonNull::new_unchecked(p as *mut dyn DynSuspCellTransform<'l, S>))
            },
            result,
            f,
            _phantom_f: PhantomData,
            _phantom_pinned: PhantomPinned,
        }))
    }
}

impl<'l, 'm, S, T, B, F> SuspCellTransformer<'m, 'l, S, T, B, F> {
    unsafe fn get_prev_mut(
        &self,
    ) -> Option<&mut (dyn DynTypedSuspCellTransform<'l, S, T, B, F> + 'l)> {
        match self.prev {
            Some(p) => unsafe { Some(&mut *p.get()) },
            None => None,
        }
    }
}

impl<'l, S, T, B, F> SuspCellTransformShared<'l, S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn continue_with<'m>(self: Pin<&'m mut Self>) -> SuspCellTransformer<'m, 'l, S, T, B, F> {
        let ptr: &'l mut _ = unsafe { &mut *self.0.get() };
        let start = ptr.start;

        if let Some(result) = take_result(&mut ptr.result) {
            SuspCellTransformer {
                start,
                prev: None,
                result: Ok(result),
            }
        } else {
            let prev = unsafe { ptr.prev.unwrap().as_mut() };
            prev.set_next_is_boxed(ptr.boxed);
            prev.set_next(Some(unsafe {
                NonNull::new_unchecked(ptr as &'l mut (dyn DynSuspCellTransform<'l, S> + 'l))
            }));

            SuspCellTransformer {
                start,
                prev: Some(unsafe { &Pin::into_inner_unchecked(self).0 }),
                result: Err(State::Unfilled),
            }
        }
    }
}

impl<'l, S, T, B, F> SuspCellInitialTransform<S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn initial(f: F) -> Self {
        SuspCellInitialTransform {
            needs_more: true,
            next_is_boxed: false,
            next: None,
            result: Err(State::Unfilled),
            f: Some(f),
            _phantom_f: PhantomData,
            _phantom_pinned: PhantomPinned,
        }
    }
}

trait Continuation<B, T> {
    fn transform(self, val: impl InBox<B>) -> T;
}

impl<B> Continuation<B, B> for () {
    fn transform(self, val: impl InBox<B>) -> B {
        InBox::take(val)
    }
}

impl<F, B, T> Continuation<B, T> for F
where
    F: FnOnce(B) -> T,
{
    fn transform(self, val: impl InBox<B>) -> T {
        self(InBox::take(val))
    }
}

impl<F, S, T, B> InternalOutFn<B> for SuspCellInner<S, T, B, F>
where
    F: Continuation<B, T>,
{
    fn write<'m>(&mut self, input: OutFnInput<'m, B>) {
        match input {
            OutFnInput::Unfilled => {
                self.transform.get_mut().result = Err(State::Unfilled);
            }
            OutFnInput::Write(x) => {
                let initial_transform = self.transform.get_mut();
                let t = initial_transform
                    .f
                    .take()
                    .unwrap()
                    .transform(unsafe { InBoxWrapper::new(x) });
                initial_transform.result = Ok(t);

                if let Some(s) = transform_all(initial_transform) {
                    let target: &mut Result<S, State> = &mut self.target;
                    *target = Ok(s);
                }
            }
        }
    }
}

/// Using the result in the given input, run all transforms available in the list.
///
/// The given input must already have its result available.
fn transform_all<'l, S>(mut transform: &mut (dyn DynSuspCellTransform<'l, S> + 'l)) -> Option<S>
where
    S: 'l,
{
    while transform.needs_more() {
        let next = transform.next();
        let src = transform.get_result();

        let next = if let Some(mut n) = next {
            unsafe { n.as_mut() }
        } else {
            return None;
        };

        unsafe {
            next.transform(src);
        }
        transform.release_result();

        transform = next;
    }

    let s = unsafe { ptr::read(transform.get_result() as *mut S) };
    transform.release_result();
    Some(s)
}

impl<'l, S, T, B, F> DynSuspCellInner<'l, S> for SuspCellInner<S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn get_transform_mut<'m>(&'m mut self) -> &'m mut dyn DynSuspCellTransform<'l, S>
    where
        'l: 'm,
    {
        self.transform.get_mut()
    }

    fn get_target_mut(&mut self) -> &mut Result<S, State> {
        &mut self.target
    }
}

impl<'l, S, T, B, F> DynSuspCellTransform<'l, S> for SuspCellTransform<'l, S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn next(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>> {
        self.next
    }

    fn set_next(&mut self, next: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>) {
        self.next = next;
    }

    fn prev(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>> {
        self.prev
    }

    fn set_prev(&mut self, prev: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>) {
        self.prev = prev;
    }

    fn is_transformed(&self) -> bool {
        !self.result.as_ref().is_err_and(|e| *e == State::Unfilled)
    }

    unsafe fn transform(&mut self, src: *mut ()) {
        let src = src as *mut B;
        let f = self.f.take().unwrap();
        let t = f.transform(unsafe { InBoxWrapper::new(&mut *src) as InBoxWrapper<'_, B> });
        self.result = Ok(t);
    }

    fn get_result(&mut self) -> *mut () {
        self.result.as_mut().unwrap() as *mut T as *mut ()
    }

    fn release_result(&mut self) {
        unsafe {
            ptr::write(&mut self.result, Err(State::Released));
        }
    }

    fn needs_more(&self) -> bool {
        self.needs_more
    }

    fn next_is_boxed(&self) -> bool {
        self.next_is_boxed
    }

    fn set_next_is_boxed(&mut self, is_boxed: bool) {
        self.next_is_boxed = is_boxed;
    }

    fn move_to_box(&mut self) -> Box<dyn DynSuspCellTransform<'l, S> + 'l> {
        Box::new(SuspCellTransform {
            start: self.start,
            needs_more: self.needs_more,
            boxed: true,
            next_is_boxed: self.next_is_boxed,
            next: None,
            prev: None,
            result: mem::replace(&mut self.result, Err(State::Released)),
            f: self.f.take(),
            _phantom_f: PhantomData,
            _phantom_pinned: PhantomPinned,
        })
    }
}

impl<'l, S, T, B, F> DynTypedSuspCellTransform<'l, S, T, B, F> for SuspCellTransform<'l, S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn needs_more_mut(&mut self) -> &mut bool {
        &mut self.needs_more
    }

    fn is_boxed(&self) -> bool {
        self.boxed
    }

    fn next_is_boxed_mut(&mut self) -> &mut bool {
        &mut self.next_is_boxed
    }

    fn result_mut(&mut self) -> &mut Result<T, State> {
        &mut self.result
    }

    fn f_mut(&mut self) -> &mut Option<F> {
        &mut self.f
    }
}

impl<'l, S, T, B, F> DynSuspCellTransform<'l, S> for SuspCellInitialTransform<S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn next(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>> {
        unsafe { mem::transmute(self.next) }
    }

    fn set_next(&mut self, next: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>) {
        unsafe { self.next = mem::transmute(next) };
    }

    fn prev(&self) -> Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>> {
        None
    }

    fn set_prev(&mut self, _: Option<NonNull<dyn DynSuspCellTransform<'l, S> + 'l>>) {}

    fn is_transformed(&self) -> bool {
        !self.result.as_ref().is_err_and(|e| *e == State::Unfilled)
    }

    unsafe fn transform(&mut self, src: *mut ()) {
        let src = src as *mut B;
        let f = self.f.take().unwrap();
        let t = f.transform(unsafe { InBoxWrapper::new(&mut *src) as InBoxWrapper<'_, B> });
        self.result = Ok(t);
    }

    fn get_result(&mut self) -> *mut () {
        self.result.as_mut().unwrap() as *mut T as *mut ()
    }

    fn release_result(&mut self) {
        unsafe {
            ptr::write(&mut self.result, Err(State::Released));
        }
    }

    fn needs_more(&self) -> bool {
        self.needs_more
    }

    fn next_is_boxed(&self) -> bool {
        self.next_is_boxed
    }

    fn set_next_is_boxed(&mut self, is_boxed: bool) {
        self.next_is_boxed = is_boxed;
    }

    fn move_to_box(&mut self) -> Box<dyn DynSuspCellTransform<'l, S> + 'l> {
        panic!("InitialTransform should never be moved into a box")
    }
}

impl<'l, S, T, B, F> DynTypedSuspCellTransform<'l, S, T, B, F>
    for SuspCellInitialTransform<S, T, B, F>
where
    F: Continuation<B, T> + 'l,
    S: 'l,
    T: 'l,
    B: 'l,
{
    fn needs_more_mut(&mut self) -> &mut bool {
        &mut self.needs_more
    }

    fn is_boxed(&self) -> bool {
        false
    }

    fn next_is_boxed_mut(&mut self) -> &mut bool {
        &mut self.next_is_boxed
    }

    fn result_mut(&mut self) -> &mut Result<T, State> {
        &mut self.result
    }

    fn f_mut(&mut self) -> &mut Option<F> {
        &mut self.f
    }
}

impl<'l, S, T, B, F> Drop for SuspCellTransform<'l, S, T, B, F> {
    fn drop(&mut self) {
        if self.next_is_boxed {
            if let Some(next) = self.next {
                let next = unsafe { Box::from_raw(next.as_ptr()) };
                mem::drop(next)
            }
        }
    }
}

impl<S, T, B, F> Drop for SuspCellInitialTransform<S, T, B, F> {
    fn drop<'l>(&'l mut self) {
        if self.next_is_boxed {
            if let Some(next) = self.next {
                let ptr: *mut (dyn DynSuspCellTransform<'l, S> + 'l) =
                    unsafe { mem::transmute(next.as_ptr()) };
                let next = unsafe { Box::from_raw(ptr) };
                mem::drop(next)
            }
        }
    }
}

struct InBoxWrapper<'l, B: ?Sized>(&'l mut B);

impl<'l, B: ?Sized> InBoxWrapper<'l, B> {
    unsafe fn new(from: &'l mut B) -> Self {
        InBoxWrapper(from)
    }
}

impl<'l, B: ?Sized> InBox<B> for InBoxWrapper<'l, B> {
    fn deref(src: &Self) -> &B {
        &*src.0
    }

    fn deref_mut(src: &mut Self) -> &mut B {
        &mut *src.0
    }

    fn forget_and_release(_: Self) {}
}

fn take_result<T>(result: &mut Result<T, State>) -> Option<T> {
    if let Ok(_) = *result {
        mem::replace(result, Err(State::Released)).ok()
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use std::pin;

    use crate::Mutate;

    use super::SuspCell;

    #[test]
    fn test_simple() {
        let mut cell = SuspCell::new(5);

        let mut b = cell.borrow_mut();
        *b = 6;
        b.release();

        let result = cell.into_inner();
        assert_eq!(result, 6);
    }

    #[test]
    fn test_inference() {
        let mut cell = SuspCell::new(5);
        let mut b = cell.borrow_mut();
        let (mut b, _) = b.replace(true);
        *b = false;
        b.release();

        assert_eq!(cell.into_inner(), false);
    }

    #[test]
    fn test_transform_inference() {
        let mut cell = SuspCell::new(5);
        {
            let (mut t, mut b) = cell.borrow_and_transform();
            let x = *b;
            let (mut b, _) = b.replace(x as f64);
            b.release();

            defer! { t: bool = t == 5.0; }
            t.release();
        }
        assert_eq!(cell.into_inner(), true);
    }

    #[test]
    fn test_transform_explicit_pin() {
        let mut cell = SuspCell::new(5);
        {
            let (mut t, mut b) = cell.borrow_and_transform();
            let x = *b;
            let (mut b, _) = b.replace(x as f64);
            b.release();

            let t = pin::pin!(t.transform(|t| t == 5.0));
            let t = t.continue_with();

            t.release();
        }
        assert_eq!(cell.into_inner(), true);
    }

    #[test]
    fn test_with() {
        let mut cell: SuspCell<bool, _, _, _, _> = SuspCell::new_with(5, |i: f32| i as f64);
        {
            let (mut t, mut b) = cell.borrow_and_transform();
            let x = *b;
            let (mut b, _) = b.replace(x as f32);
            b.release();

            defer! { t: bool = t == 5.0; }
            t.release();
        }

        assert_eq!(cell.into_inner(), true);
    }

    #[test]
    fn test_with_inference() {
        let mut cell = SuspCell::new_with(5, |i: f32| i as f64);
        {
            let (mut t, mut b) = cell.borrow_and_transform();
            let x = *b;
            let (mut b, _) = b.replace(x as f32);
            b.release();

            defer! { t = t == 5.0; }
            t.release();
        }

        assert_eq!(cell.into_inner(), true);
    }
}
