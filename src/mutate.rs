use std::{marker::PhantomData, mem::{self, ManuallyDrop, MaybeUninit}, ops::{Deref, DerefMut}, pin::Pin};

/// Trait representing references that currently contain
/// one type but expect another before being dropped.
///
/// A Drop implementation is required that ensures that the
/// referenced cell is poisoned if it cannot be filled with
/// the requested type. The current `A` value must also be arranged
/// to be dropped, whether at this time or when the referenced cell gets dropped.
/// If the implementer has a means of determining that
/// the request can be filled at drop-time, they may do so.
/// On nightly, implementers are encouraged to use specialization to do so.
/// However, users should not rely on this.
///
/// For now, users should always call `release` or `into_amut` explicitly.
///
/// `A` must be pinned in memory. For that reason, the `into_pin` method
/// must be valid.
///
/// Unsized A and B will eventually be supported in combination with unsized rvalues.
pub trait Mutate<A, B = A>: Sized + Deref<Target = A> + DerefMut + Drop {

    /// Like take, but it leaves knowledge of the actual size.
    ///
    /// The resulting MaybeUninit<A> is guaranteed to be uninitialized.
    fn take_and_uninit(self) -> (impl Mutate<MaybeUninit<A>, B>, A);

    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    ///
    /// `A` must be dropped in place.
    fn set_pin<C>(pin: Pin<Self>, val: C) -> Pin<impl Mutate<C, B>>;

    fn release(self) where A: Is<B>;


    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    fn set<C>(self, val: C) -> impl Mutate<C, B> {
        let p = self.into_pin();
        let p = Self::set_pin(p, val);
        unsafe { Pin::into_inner_unchecked(p) }
    }

    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    fn replace<C>(self, val: C) -> (impl Mutate<C, B>, A) {
        let (m, a) = self.take_and_uninit();
        (m.set(val), a)
    }

    fn take(self) -> (impl Mutate<(), B>, A) {
        self.replace(())
    }

    /// This method will eventually be required for Unsized B.
    fn set_and_release(self, val: B) -> () {
        let m = self.set(val);
        m.release();
    }

    fn into_pin(self) -> Pin<Self> {
        unsafe {
            Pin::new_unchecked(self)
        }
    }

    fn set_and_release_pin(pin: Pin<Self>, val: B) -> () {
        let m = Self::set_pin(pin, val);
        unsafe { Pin::into_inner_unchecked(m).release() }
    }

    fn map<C>(self, f: impl FnOnce(A) -> C) -> impl Mutate<C, B> {
        let (r, a) = self.replace(());
        let c = f(a);
        r.replace(c).0
    }

    fn into_amut<'l>(self) -> AMut<'l, impl Mutate<A, B>, A, B> where A: Is<B>, Self: 'l {
        AMut {
            phantom_a: PhantomData,
            phantom_b: PhantomData,
            mutate: ManuallyDrop::new(self) }
    }
}

/// Short for "Affine Mutate"
///
/// The trait of `Mutate` instances that can safely be allowed
/// to drop automatically.
pub trait AMutate<A, B = A>: Mutate<A, B> where A: Is<B> {}

/// Short for "Affine Mut".
///
/// It requires a Mutable<A, B> instance where A: Is<B>,
/// but in exchange automatically calls release upon drop.
pub struct AMut<'l, M, A, B = A> where M: Mutate<A, B> + 'l, A: Is<B> {
    phantom_a: PhantomData<&'l mut A>,
    phantom_b: PhantomData<&'l mut B>,
    mutate: ManuallyDrop<M>
}

impl<'l, A, B, M> Drop for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> {
    fn drop(&mut self) {
        unsafe {
            let m = ManuallyDrop::take(&mut self.mutate);
            m.release()
        }
    }
}

impl<'l, A, B, M> Deref for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> {
    type Target = M::Target;

    fn deref(&self) -> &A {
        &self.mutate
    }
}

impl<'l, A, B, M> DerefMut for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> {
    fn deref_mut(&mut self) -> &mut A {
        &mut self.mutate
    }
}

impl<'l, A, B, M> Mutate<A, B> for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> {
    fn take_and_uninit(mut self) -> (impl Mutate<MaybeUninit<A>, B>, A) {
        let result = unsafe {
            ManuallyDrop::take(&mut self.mutate).take_and_uninit()
        };
        mem::forget(self);
        result
    }

    fn set_pin<C>(pin: Pin<Self>, val: C) -> Pin<impl Mutate<C, B>> {
        unsafe {
            let mut a = Pin::into_inner_unchecked(pin);
            let m = Pin::new_unchecked(ManuallyDrop::take(&mut a.mutate));
            let result = M::set_pin(m, val);
            mem::forget(a);
            result
        }
    }

    fn release(self) where A: Is<B> {
        mem::drop(self)
    }

    fn into_amut<'m>(self) -> AMut<'m, impl Mutate<A, B>, A, B> where A: Is<B>, 'l: 'm {
        self
    }
}

impl<'l, A, B, M> AMutate<A, B> for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> {}


/// Trait that determines whether a type is itself.
///
/// Do not add additional impls.
pub trait Is<T: ?Sized>: private::Private<T> {
    fn id(self) -> T where T: Sized;
    fn id_ref(&self) -> &T;
    fn id_mut(&mut self) -> &mut T;
    fn id_ptr(ptr: *const Self) -> *const T;
    fn id_ptr_mut(ptr: *mut Self) -> *mut T;
}

impl<A: ?Sized> Is<A> for A {
    fn id(self) -> A where A: Sized {
        self
    }

    fn id_ref(&self) -> &A {
        self
    }

    fn id_mut(&mut self) -> &mut A {
        self
    }

    fn id_ptr(ptr: *const A) -> *const A {
        ptr
    }

    fn id_ptr_mut(ptr: *mut Self) -> *mut A {
        ptr
    }
}

impl<A: ?Sized> private::Private<A> for A {}

mod private {
    pub trait Private<T: ?Sized> {}
}
