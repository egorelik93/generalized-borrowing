#![cfg_attr(not(doctest), doc = include_str!("../README.md"))]

use std::mem::ManuallyDrop;

pub mod mutate;

pub use mutate::{Mutate, AMutate, AMut};

union Typestate<A, B> {
    current: ManuallyDrop<A>,
    target: ManuallyDrop<B>
}


#[cfg(test)]
mod tests {
    use super::*;

    fn it_compiles<'l, A>(a : impl AMutate<'l, A>) {
        a.release();
    }
}
