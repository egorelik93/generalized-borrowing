#![cfg_attr(not(doctest), doc = include_str!("../README.md"))]

#![cfg_attr(feature = "nightly", feature(allocator_api))]
#![cfg_attr(feature = "nightly", feature(unsized_locals))]
#![cfg_attr(feature = "nightly", feature(unsized_fn_params))]
#![cfg_attr(feature = "nightly", feature(specialization))]
#![cfg_attr(feature = "nightly", feature(super_let))]

use std::mem::ManuallyDrop;

pub mod mutate;
pub mod mutref;
mod pinned;
pub mod inout;
mod susp;

pub use mutate::{Mutate, AMutate, AMut, Is};
pub use inout::{Input, Output, InOut, InBox, OutFn};
pub use mutref::{Mut, In, Out, MutateCell};
pub use pinned::PinnedCell;
pub use susp::{SuspCell, SuspCellRef, SuspCellTransformer};

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
