use std::{mem::{ManuallyDrop, MaybeUninit}, ptr};

use crate::{mutref::{OutFn, OutFnInput}, Mut, Typestate};

pub struct PinnedCell<A, B> {
    val: MaybeUninit<Typestate<A, B>>,
    inner: PinnedCellInner
}

struct PinnedCellInner { written: bool }

impl<B> OutFn<B> for PinnedCellInner {
    fn write<'m>(&mut self, input: OutFnInput<'m, B>) {
        self.written = match input { OutFnInput::Write(_) => true, OutFnInput::Unfilled => false };
    }
}

impl<A, B> PinnedCell<A, B> {
    pub fn new(a: A) -> Self {
        PinnedCell {
            val: MaybeUninit::new(Typestate { current: ManuallyDrop::new(a) }),
            inner: PinnedCellInner { written: false } }
    }

    pub fn borrow_mut(&mut self) -> Mut<A, B> {
        unsafe {
            Mut::from_parts(self.val.assume_init_mut(), &mut self.inner)
        }
    }

    pub fn into_inner(mut self) -> B {
        assert!(self.inner.written, "Mut was never written");
        unsafe { ManuallyDrop::take(&mut self.val.assume_init_mut().target) }
    }
}

impl<A, B> Drop for PinnedCell<A, B> {
    fn drop(&mut self) {
        assert!(self.inner.written, "Mut was never written");

        unsafe { ptr::drop_in_place(&mut *self.val.assume_init_mut().target); }
    }
}
