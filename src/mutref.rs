use std::{any::Any,
          cmp,
          marker::PhantomData,
          mem::{self, ManuallyDrop, MaybeUninit},
          ops::{Deref, DerefMut},
          panic::{catch_unwind, UnwindSafe},
          pin::Pin,
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
    //write: OutFn<'a, B>,
    write: &'a mut dyn OutFn<B>
}

impl<'l, A, B> Mut<'l, A, B> {
    pub(crate) unsafe fn from_parts<F>(val: &'l mut Typestate<A, B>, write: &'l mut F) -> Self where F: OutFn<B> {
        Mut {
            val: unsafe { mem::transmute(val) },
            write: write as &mut dyn OutFn<B>
        }
    }
}

impl<A, B> Drop for Mut<'_, A, B> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(self.val);
        }
        self.write.write(OutFnInput::Unfilled);
    }
}

impl<A, B> Deref for Mut<'_, A, B> {
    type Target = A;

    fn deref(&self) -> &A {
        unsafe {
            &self.val
        }
    }
}

impl<A, B> DerefMut for Mut<'_, A, B> {
    fn deref_mut(&mut self) -> &mut A {
        unsafe {
            &mut self.val
        }
    }
}


impl<'l, A, B> Mutate<A, B> for Mut<'l, A, B> {

    fn take_and_uninit<'m>(self) -> (impl Mutate<MaybeUninit<A>, B> + 'm, A) where 'l: 'm {
        let transmuted: Mut<MaybeUninit<A>, B> = unsafe { mem::transmute(self) };
        let a = mem::replace(transmuted.val, MaybeUninit::uninit());
        unsafe {
            (transmuted, a.assume_init())
        }
    }

    fn set_pin<'m, C>(pin: Pin<Self>, val: C) -> Pin<impl Mutate<C, B> + 'm> where 'l: 'm, C: 'm {
        const {
            assert!(mem::size_of::<C>() <= size_of_union::<A, B>());
        }

        unsafe {
            let mut m = Pin::into_inner_unchecked(pin);
            ptr::drop_in_place(&mut m.val);

            mem::replace(mem::transmute(&mut m.val), MaybeUninit::new(val));
            let transmuted: Mut<'m, C, B> = mem::transmute(m);
            Pin::new_unchecked(transmuted)
        }
    }

    fn release(mut self) where A: Is<B> {
        unsafe {
            let a = &mut *self.val;
            let b = a.id_mut();
            self.write.write(OutFnInput::Write(b));
        }

        mem::forget(self);
    }
}

impl<A, B> UnwindSafe for Mut<'_, A, B> {}


/// An In<A> is like a Box, but isn't necessarily stored
/// on the heap.
pub type In<'a, A> = Mut<'a, A, ()>;

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
        let closure = &mut self.inner as &mut dyn OutFn<B>;
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

pub(crate) trait OutFn<B> {
    fn write<'m>(&mut self, input: OutFnInput<'m, B>);
}

impl<A, B, M> OutFn<B> for MutateCellInner<M, A, B> where M: Mutate<A, B> {
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
