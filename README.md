# generalized-borrowing

A Rust port of borrowing features designed for a new linearly-typed programming language.

The original formulation is based on a pair of objects
```
{ read: Susp<T>, write: &'read out T }
```
with the functions
```
alloca : () ->  { read: Susp<T>, write: &'read out T };
write: { write: &out T, val: T } -> () where 'write: 'val;
```

This is based on the theory of dualizable objects in Category Theory:
`T` has as its dual object `&out T`.
The theory requires that both sides support a map-like operation, and that mapping to ()
allows the lifetime to be dropped;
while this is trivial for the write side, for the read side this is expensive at runtime.
For that reason, we make it optional, replacing `T` with `Susp<T>` on the read side.

`Susp<T>` is a type that can be mapped to any `Susp<X>`, and it will arrange that
the mapping gets run as soon as `&out T` gets written to.
There is also a more efficient `Pinned<T>` that does not allow mapping beyond an optional
initial closure. In either case, we can use this to run cleanup code after write, giving
`&out T` the character of an `FnOnce(T) -> ()`.

In the original formulation, once `&out T` is written to and the lifetime dropped, `Susp<X>`
or `Pinned<X>` can be consumed and have the value of `X` extracted.
Since Rust does not have self-referential structs, the role of `Susp<T>` is split in two: an
anchor cell and a transformer. `Pinned<T>` does not require a transformer.

We can generalize this a bit further to borrowing existing values;
given an `A`, we can borrow it as `&mut A/B`.

```
borrow : A ->  { read: Susp<B>, write: &'read mut A/B };
replace: { write: &mut A/B, val: B } -> A where 'write: 'val;
```

`&out B` is then just a synonym for `&mut ()/B`. Similarly, we can have an `&in A` that is synonymous
with `&mut A/()`.
Because we can specify cleanup code, we can do things like borrow `A` or `Box<A>` as `&in A`.
However, this cleanup code also means that `&mut A/A` is not quite the same as Rust's `&mut A`.

This is heavily inspired by typestate and session types. The innovation is that combining them with a lifetime
system allows extending them to cover reference/pointer types on the stack, as well as other effects.

Since Rust does not support true linear types, there are limits to how much can be ported.
Instead, dropped writers or transformers will poison the read/anchor side.
