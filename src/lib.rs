#![cfg_attr(not(doctest), doc = include_str!("../README.md"))]

use std::mem::ManuallyDrop;

pub mod mutate;
pub mod mutref;
mod pinned;

pub use mutate::{Mutate, AMutate, AMut};
pub use mutref::{Mut, In, Out, MutateCell};
pub use pinned::PinnedCell;

union Typestate<A, B> {
    current: ManuallyDrop<A>,
    target: ManuallyDrop<B>
}


#[cfg(test)]
mod tests {
    use super::*;

    fn it_compiles<A>(a : impl AMutate<A>) {
        a.release();
    }
}
