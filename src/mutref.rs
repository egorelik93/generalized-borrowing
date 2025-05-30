use std::{convert::Infallible,
          marker::PhantomData,
          mem::{self, ManuallyDrop, MaybeUninit},
          ops::{Deref, DerefMut},
          panic::UnwindSafe,
          ptr};

use crate::Typestate;
use crate::mutate::{Mutate, Is};

const fn size_of_union<A, B>() -> usize {
    let size_a = size_of::<A>();
    let size_b = size_of::<B>();
    if size_a < size_b { size_b } else { size_a }
}


pub struct Mut<'a, A, B = A> {
    val: &'a mut A,
    // For pinned, we can use &'a mut, but in order to satisfy Rust's
    // aliasing rules in Susp, we cannot store an &'a mut.
    write: *mut (dyn InternalOutFn<B> + 'a)
}

impl<'l, A, B> Mut<'l, A, B> {
    pub(crate) unsafe fn from_parts<F>(val: &'l mut Typestate<A, B>, write: &'l mut F) -> Self where F: InternalOutFn<B> {
        Mut {
            val: unsafe { mem::transmute(val) },
            write: write as *mut (dyn InternalOutFn<B> + 'l)
        }
    }

    pub(crate) unsafe fn from_raw_parts<F>(val: &'l mut Typestate<A, B>, write: *mut F) -> Self where F: InternalOutFn<B> {
        Mut {
            val: unsafe { mem::transmute(val) },
            write: write as *mut (dyn InternalOutFn<B> + 'l)
        }
    }
}

impl<A, B> Drop for Mut<'_, A, B> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.val);
            (&mut *self.write).write(OutFnInput::Unfilled);
        }
    }
}

impl<A, B> Deref for Mut<'_, A, B> {
    type Target = A;

    fn deref(&self) -> &A {
        &self.val
    }
}

impl<A, B> DerefMut for Mut<'_, A, B> {
    fn deref_mut(&mut self) -> &mut A {
        &mut self.val
    }
}


impl<'l, A, B> Mutate<A, B> for Mut<'l, A, B> {
    type Ref<'m, S> = Mut<'m, S, B> where Self: 'm, S: 'm;
    type Err = Infallible;

    fn write<'m, C>(self, src: C) -> Self::Ref<'m, C> where Self: 'm {
        const {
            assert!(mem::size_of::<C>() <= size_of_union::<A, B>());
        }

        let transmuted: Mut<MaybeUninit<C>, B> = unsafe { mem::transmute(self) };
        *transmuted.val = MaybeUninit::new(src);
        unsafe { mem::transmute(transmuted) }
    }

    fn release(self) -> Result<(), Infallible> where A: Is<B> {
        unsafe {
            let a = &mut *self.val;
            let b = a.id_mut();
            (&mut *self.write).write(OutFnInput::Write(b));
        }

        mem::forget(self);
        Ok(())
    }
}

impl<A, B> UnwindSafe for Mut<'_, A, B> {}


/// An In<A> is like a Box, but isn't necessarily stored
/// on the heap.
pub type In<'a, A> = crate::inout::DisposableInput<Mut<'a, A, ()>, A>;

pub type Out<'a, A> = Mut<'a, (), A>;

pub(crate) enum OutFnInput<'l, T> {
    Write(&'l mut T),
    Unfilled
}

pub struct MutateCell<M, A, B> where M: Mutate<A, B> {
    val: MaybeUninit<Typestate<A, B>>,
    inner: MutateCellInner<M, A, B>,
}

impl<A, B, M> MutateCell<M, A, B> where M: Mutate<A, B> {
    pub fn new(m : M) -> Self {
        MutateCell {
            val: MaybeUninit::uninit(),
            inner: MutateCellInner {
                m: ManuallyDrop::new(m),
                written: false,
                phantom_a: PhantomData,
                phantom_b: PhantomData }
        }
    }

    pub fn borrow_mut(&mut self) -> Mut<A, B> {
        let closure = &mut self.inner as &mut dyn InternalOutFn<B>;
        let a = unsafe { &mut *self.val.assume_init_mut().current };

        Mut {
            val: a,
            write: closure
        }
    }
}

impl<A, B, M> Drop for MutateCell<M, A, B> where M: Mutate<A, B> {
    fn drop(&mut self) {
        assert!(self.inner.written, "Mut was never written to");
    }
}

struct MutateCellInner<M, A, B> where M: Mutate<A, B> {
    m: ManuallyDrop<M>,
    written: bool,
    phantom_a: PhantomData<A>,
    phantom_b: PhantomData<*mut B>
}

pub(crate) trait InternalOutFn<B> {
    fn write<'m>(&mut self, input: OutFnInput<'m, B>);
}

impl<A, B, M> InternalOutFn<B> for MutateCellInner<M, A, B> where M: Mutate<A, B> {
    fn write<'m>(&mut self, input: OutFnInput<'m, B>) {
        self.fill(input);
    }
}

impl<A, B, M> MutateCellInner<M, A, B> where M: Mutate<A, B> {

    fn fill<'m>(&mut self, i: OutFnInput<'m, B>) -> () {
        match i {
            OutFnInput::Write(b) => unsafe {
                let m = ManuallyDrop::take(&mut self.m);
                m.set(ptr::read(b));
                self.written = true;
            },
            OutFnInput::Unfilled => {
                self.written = false;
            }
        }
    }
}
