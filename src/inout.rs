use std::{
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    ops::{Deref, DerefMut},
    ptr};

use crate::{Mutate, Is};

/// Conceptually, this is like an extremely simplified form of Mutate<A, ()>.
///
/// It is formulated to allow us to define OutFn.
/// Otherwise, avoid using this.
/// Due to blanket impls, we cannot automatically implement this for Mutate<A, ()>,
/// but any Mutate<A, ()> can be explicitly turned into one using `from`.
pub trait InBox<A: ?Sized> {
    fn deref(src: &Self) -> &A;

    fn deref_mut(src: &mut Self) -> &mut A;

    fn forget_and_release(src: Self) where Self: Sized;

    fn take(self) -> A where Self: Sized, A: Sized {
        let a = unsafe { ptr::read(Self::deref(&self)) };
        Self::forget_and_release(self);
        a
    }

    fn from<M>(from: M) -> impl InBox<A> where M: Sized + Mutate<A, ()> {
        DisposableInput::new(from)
    }
}

/// Semantically, the core portion of `Output<B>`.
pub trait OutFn<B: ?Sized>: Drop {
    type Err;

    fn release_from(self, from: impl InBox<B>) -> Result<(), Self::Err>;
}

impl<T: ?Sized> InBox<T> for T {
    fn deref(src: &Self) -> &T {
        src
    }

    fn deref_mut(src: &mut Self) -> &mut T {
        src
    }

    fn forget_and_release(src: Self) where Self: Sized {
        mem::forget(src)
    }
}


/// In the original formulation, equivalent to `Mutate<A, ()>`.
///
/// In this Rust port, they differ only in that an `Input<A>` must
/// be safe to drop, unlike `Mutate<A, ()>` on stable.
pub trait Input<A: ?Sized>: Mutate<A, ()> {
    fn from(from: impl Mutate<A, ()>) -> impl Input<A> {
        DisposableInput::new(from)
    }
}

pub(crate) struct DisposableInput<M, A> where M: Mutate<A, ()>, A: ?Sized {
    mutate: ManuallyDrop<M>,
    phantom: PhantomData<A>
}

impl<M, A> DisposableInput<M, A> where M: Mutate<A, ()>, A: ?Sized {
    pub(crate) fn new(from: M) -> Self {
        DisposableInput { mutate: ManuallyDrop::new(from), phantom: PhantomData }
    }
}

impl<M, A> Drop for DisposableInput<M, A> where M: Mutate<A, ()> , A: ?Sized {
    fn drop(&mut self) {
        unsafe {
            let m = ManuallyDrop::take(&mut self.mutate);
            m.set_and_release(());
        }
    }
}

impl<M, A> Deref for DisposableInput<M, A> where M: Mutate<A, ()> , A: ?Sized {
    type Target = A;

    fn deref(&self) -> &A {
        &*self.mutate
    }
}

impl<M, A> DerefMut for DisposableInput<M, A> where M: Mutate<A, ()> , A: ?Sized {
    fn deref_mut(&mut self) -> &mut A {
        &mut *self.mutate
    }
}

impl<M, A> Mutate<A, ()> for DisposableInput<M, A> where M: Mutate<A, ()> , A: ?Sized {
    type Ref<'l, S> = DisposableInput<M::Ref<'l, S>, S> where Self: 'l, S: 'l;
    type Err = M::Err;

    fn write<'l, C>(mut self, src: C) -> Self::Ref<'l, C> where Self: 'l {
        let m = unsafe { ManuallyDrop::take(&mut self.mutate) };
        DisposableInput::new(m.write(src))
    }

    fn release(mut self) -> Result<(), M::Err> where A: Is<()>
    {
        let m = unsafe { ManuallyDrop::take(&mut self.mutate) };
        m.release()
    }
}

impl<M, A> Input<A> for DisposableInput<M, A> where M: Mutate<A, ()>, A: ?Sized {}

impl<M, A> InBox<A> for DisposableInput<M, A> where M: Mutate<A, ()>, A: ?Sized {
    fn deref(src: &Self) -> &A {
        &*src
    }

    fn deref_mut(src: &mut Self) -> &mut A {
        &mut *src
    }

    fn forget_and_release(src: Self) where Self: Sized {
        src.write(()).release();
    }
}


/// In the original formulation, equivalent to `Mutate<(), B>`
///
/// In this Rust port, `Mutate<(), B>` does not have the `release_from`
/// method.
/// For `B: Sized`, they are equivalent.
/// To represent just the FnOnce(B) -> () semantics, use OutFn instead.
pub trait Output<B: ?Sized>: Mutate<(), B> + OutFn<B, Err = <Self as Mutate<(), B>>::Err> {}

impl<B, M> OutFn<B> for M where M: Mutate<(), B> {
    type Err = M::Err;

    fn release_from(self, from: impl InBox<B>) -> Result<(), M::Err>{
        let b = from.take();
        <M as Mutate<(), B>>::set_and_release(self, b)
    }
}

impl<B, M> Output<B> for M where M: Mutate<(), B> {}


/// Conceptually a pair `(Input<A>, Output<B>)` where Output must be consumed last.
///
/// In the original formulation, all Mutate have this property.
/// In Rust, for all sized `B` they still do.
trait InOut<A: ?Sized, B: ?Sized>: Mutate<A, B> {
    type RefIO<'l, S>: InOut<S, B> where Self: 'l, S: 'l;

    /// Ensures that M::Ref implements InOut.
    //
    // A bit hackish and inconvenient for users, but should be good enough.
    fn downcast_ref<'l, S>(from: Self::Ref<'l, S>) -> Self::RefIO<'l, S>;

    fn release_from(self, from: impl InBox<B>) -> Result<(), Self::Err>;
}

impl<A, B, M> InOut<A, B> for M where M: Mutate<A, B>, A: ?Sized {
    type RefIO<'l, S> = M::Ref<'l, S> where M: 'l, S: 'l;

    fn downcast_ref<'l, S>(from: M::Ref<'l, S>) -> M::Ref<'l, S> {
        from
    }

    fn release_from(self, from: impl InBox<B>) -> Result<(), M::Err>{
        let b = unsafe { ptr::read(InBox::deref(&from)) };
        InBox::forget_and_release(from);
        let m = self.set(b);
        m.release()
    }
}
