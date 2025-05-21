use std::{ops::{Deref, DerefMut}, mem::{self, ManuallyDrop}, marker::PhantomData};

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
pub trait Mutate<'l, A: ?Sized, B: ?Sized = A>: Sized + Deref<Target = A> + DerefMut + Drop {
    type Ref<'m, S, T>: Mutate<'m, S, T> where S: ?Sized, T: ?Sized;

    /// size_of<C>() must be smaller than max(size_of<A>(), size_of<B>())
    fn replace_type<C>(self, val: C) -> (Self::Ref<'l, C, B>, A) where A: Sized, C: Sized;
    fn release(self) where A: Is<B>;

    fn take(self) -> (Self::Ref<'l, (), B>, A) where A: Sized {
        self.replace_type(())
    }

    fn map<C>(self, f: impl FnOnce(A) -> C) -> impl Mutate<'l, C, B> where A: Sized {
        let (r, a) = self.replace_type(());
        let c = f(a);
        r.replace_type(c).0
    }

    fn into_amut(self) -> AMut<'l, impl Mutate<'l, A, B>, A, B> where A: Is<B> {
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
pub trait AMutate<'l, A: ?Sized, B: ?Sized = A>: Mutate<'l, A, B> {}

/// Short for "Affine Mut".
///
/// It requires a Mutable<A, B> instance where A: Is<B>,
/// but in exchange automatically calls release upon drop.
pub struct AMut<'l, M, A, B = A> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {
    phantom_a: PhantomData<&'l mut A>,
    phantom_b: PhantomData<&'l mut B>,
    mutate: ManuallyDrop<M>
}

impl<'l, A, B, M> Drop for AMut<'l, M, A, B> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {
    fn drop(&mut self) {
        unsafe {
            let m = ManuallyDrop::take(&mut self.mutate);
            m.release()
        }
    }
}

impl<'l, A, B, M> Deref for AMut<'l, M, A, B> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {
    type Target = M::Target;

    fn deref(&self) -> &A {
        &self.mutate
    }
}

impl<'l, A, B, M> DerefMut for AMut<'l, M, A, B> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {
    fn deref_mut(&mut self) -> &mut A {
        &mut self.mutate
    }
}

impl<'l, A, B, M> Mutate<'l, A, B> for AMut<'l, M, A, B> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {
    type Ref<'m, S: ?Sized, T: ?Sized> = M::Ref<'m, S, T>;

    fn replace_type<C>(mut self, val: C) -> (M::Ref<'l, C, B>, A) where A: Sized, C: Sized {
        let result = unsafe {
            ManuallyDrop::take(&mut self.mutate).replace_type(val)
        };
        mem::forget(self);
        result
    }

    fn release(self) where A: Is<B> {
        mem::drop(self)
    }

    fn into_amut(self) -> AMut<'l, impl Mutate<'l, A, B>, A, B> where A: Is<B> {
        self
    }
}

impl<'l, A, B, M> AMutate<'l, A, B> for AMut<'l, M, A, B> where M: Mutate<'l, A, B>, A: Is<B> + ?Sized, B: ?Sized {}


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
