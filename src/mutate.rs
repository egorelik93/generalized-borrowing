use std::{marker::PhantomData, mem::{self, ManuallyDrop, MaybeUninit}, ops::{Deref, DerefMut}, pin::Pin, ptr};

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
/// While the original formulation allowed `B` to be unsized, it did not have coercions from `&mut Sized` to `&mut DST`.
/// Since Rust does have such coercions, we have the following mutually-exclusive options:
/// 1. (Eventually) allow unsized coercions in `A` and `B` simultaneously. This requires us to remove the ability
///    to directly pass an unsized `B` to the continuation/cleanup code, as having both is unsound.
/// 2. Disallow such coercions in `Mutate`, requiring users to borrow as `&mut` if they want this. This allows
///    us to keep the ability to directly pass in `B`, also keeping the semantic that `Mutate<(),B>` is like `FnOnce(B) -> ()`.
///
/// The choice we make for now is actually to not have either.
/// We have a number of reasons for this:
/// - Unsized coercions are currently locked to nightly anyway.
/// - Unsized coercions are very much covariant, but `B` here is really a contravariant parameter.
/// - The only useful combinations for unsized `B` are `&mut B/B` and `&mut ()/B`.
///   All methods on `Mutate` require the top to be `Sized` so the former
///   is basically limited in functionality to `Deref` and `DerefMut`. One may as well directly
///   borrow as Rust's `&mut B` at the time of coercion; cleanup code will still get called once the borrow
///   finishes.
///
/// Users who want (2) for unsized `B` should use `InOut<A, B>` instead.
pub trait Mutate<A, B = A>: Deref<Target = A> + DerefMut + Drop where A: ?Sized, B: ?Sized {
    type Ref<'l, S>: Mutate<S, B, Err = Self::Err> where Self: 'l, S: 'l;
    type Err;

    /// Writes without reading or dropping the current value.
    ///
    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`.
    /// This is technically safe for users to call, but implementors must be extremely careful
    /// to satisfy these requirements.
    /// The expectation is that a user or library code may unsafely drop or take the value first
    /// through a reference, and then call this method to set a new value.
    fn write<'l, C>(self, src: C) -> Self::Ref<'l, C> where Self: 'l;

    fn release(self) -> Result<(), Self::Err> where A: Is<B>;


    fn take<'l>(self) -> (Self::Ref<'l, ()>, A) where Self: 'l, A: Sized, Self: Sized {
        let a = unsafe { ptr::read(&*self) };
        (self.write(()), a)
    }

    /// Like take, but it leaves knowledge of the actual size.
    ///
    /// The resulting MaybeUninit<A> is guaranteed to be uninitialized.
    fn take_and_uninit<'l>(self) -> (Self::Ref<'l, MaybeUninit<A>>, A) where Self: 'l, A: Sized, Self: Sized {
        let a = unsafe { ptr::read(&*self) };
        (self.write(MaybeUninit::uninit()), a)
    }

    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    fn replace<'l, C>(self, val: C) -> (Self::Ref<'l, C>, A) where Self: 'l, C: 'l, A: Sized, Self: Sized {
        let a = unsafe { ptr::read(&*self) };
        (self.write(val), a)
    }

    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    ///
    /// If `A` is unsized, then `size_of::<C>()` must be smaller than `size_of::<B>()`.
    fn set<'l, C>(mut self, val: C) -> Self::Ref<'l, C> where Self: 'l, Self: Sized {
        unsafe { ptr::drop_in_place(&mut *self); }
        self.write(val)
    }

    fn map<'l, C>(self, f: impl FnOnce(A) -> C) -> Self::Ref<'l, C> where Self: 'l, C: 'l, A: Sized, Self: Sized {
        let a = unsafe { ptr::read(&*self) };
        let c = f(a);
        self.write(c)
    }

    fn set_and_release(self, val: B) -> Result<(), Self::Err> where B: Sized, Self: Sized {
        let m = self.set(val);
        m.release()
    }

    fn into_pin(self) -> Pin<Self> where Self: Sized {
        unsafe {
            Pin::new_unchecked(self)
        }
    }

    /// Writes without reading or dropping the current value.
    ///
    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`.
    fn write_pin<'l, C>(pin: Pin<Self>, src: C) -> Pin<Self::Ref<'l, C>> where Self: Sized + 'l {
        unsafe {
            let m = Pin::into_inner_unchecked(pin);
            let m = m.write(src);
            Pin::new_unchecked(m)
        }
    }

    /// `size_of::<C>()` must be smaller than `max(size_of::<A>(), size_of::<B>())`
    ///
    /// `A` must be dropped in place.
    /// If `A` is unsized, then `size_of::<C>()` must be smaller than `size_of::<B>()`.
    fn set_pin<'l, C>(pin: Pin<Self>, val: C) -> Pin<Self::Ref<'l, C>> where Self: Sized + 'l {
        unsafe {
            let m = Pin::into_inner_unchecked(pin);
            let m = m.set(val);
            Pin::new_unchecked(m)
        }
    }

    fn set_and_release_pin(pin: Pin<Self>, val: B) -> Result<(), Self::Err> where Self: Sized, B: Sized {
        let m = Self::set_pin(pin, val);
        unsafe { Pin::into_inner_unchecked(m).release() }
    }

    fn into_amut<'l>(self) -> AMut<'l, impl Mutate<A, B, Err = Self::Err>, A, B> where A: Is<B> + Sized, Self: Sized + 'l {
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
pub trait AMutate<A: ?Sized, B: ?Sized = A>: Mutate<A, B> where A: Is<B> {}

/// Short for "Affine Mut".
///
/// It requires a Mutable<A, B> instance where A: Is<B>,
/// but in exchange automatically calls release upon drop.
pub struct AMut<'l, M, A, B = A> where M: Mutate<A, B> + 'l, A: Is<B>, A: ?Sized, B: ?Sized {
    phantom_a: PhantomData<&'l mut A>,
    phantom_b: PhantomData<&'l mut B>,
    mutate: ManuallyDrop<M>
}

impl<'l, A, B, M> Drop for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> + ?Sized, B: ?Sized{
    fn drop(&mut self) {
        unsafe {
            let m = ManuallyDrop::take(&mut self.mutate);
            m.release();
        }
    }
}

impl<'l, A, B, M> Deref for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> + ?Sized, B: ?Sized {
    type Target = M::Target;

    fn deref(&self) -> &A {
        &self.mutate
    }
}

impl<'l, A, B, M> DerefMut for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> + ?Sized, B: ?Sized {
    fn deref_mut(&mut self) -> &mut A {
        &mut self.mutate
    }
}

impl<'l, A, B, M> Mutate<A, B> for AMut<'l, M, A, B> where M: Mutate<A, B> + 'l, A: Is<B> + ?Sized, B: ?Sized {
    type Ref<'m, C> = M::Ref<'m, C> where Self: 'm, C: 'm;
    type Err = M::Err;

    fn write<'m, C>(mut self, src: C) -> Self::Ref<'m, C> where Self: 'm {
        let result = unsafe {
            ManuallyDrop::take(&mut self.mutate).write(src)
        };
        mem::forget(self);
        result
    }

    fn release(mut self) -> Result<(), M::Err> where A: Is<B> {
        unsafe {
            let m = ManuallyDrop::take(&mut self.mutate);
            m.release()
        }
    }

    fn into_amut<'m>(self) -> AMut<'m, impl Mutate<A, B, Err = Self::Err>, A, B> where A: Is<B>, 'l: 'm {
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

    fn id_mutate_top<X>(m: impl Mutate<Self, X>) -> impl Mutate<T, X> where Self: Sized, T: Sized;
    fn id_mutate_bottom<X>(m: impl Mutate<X, Self>) -> impl Mutate<X, T> where Self: Sized, T: Sized;
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

    fn id_mutate_top<X>(m: impl Mutate<Self, X>) -> impl Mutate<A, X> {
        m
    }

    fn id_mutate_bottom<X>(m: impl Mutate<X, Self>) -> impl Mutate<X, A> {
        m
    }
}

impl<A: ?Sized> private::Private<A> for A {}

mod private {
    pub(crate) trait Private<T: ?Sized> {}
}
