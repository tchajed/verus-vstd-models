# Verifying Verus built-in types against a model

Currently, Verus has completely axiomatic types for `Seq`, `Set`, and `Map`:
the types are `#[verifier::external_body]`, the functions are opaque, and then
there are axioms that characterize the functions. This runs the risk of
introducing unsound axioms, since nothing checks that they make sense
collectively.

Here we _implement_ each of these types with an underlying model (with
primitives like inductive data types and functions, or `enum`s, `struct`s, and
`spec_fn`s in Verus parlance). This does not introduce any additional axioms or
trust, we just rely on the existing data types. It also means that we can try
adding new lemmas or strengthening the existing ones by removing preconditions
without fear; if we can prove the new lemma, it's definitely safe to keep. (At
least for soundness - we still have to think about triggers and automation
performance to avoid making users' proofs slower.)

There are some limitations around `#[verifier(broadcast_forall)]` that make
this not work as a drop-in replacement: the lemmas can be marked
`broadcast_forall`, but users have to call `reveal` to use the lemmas (rather
than them being always available), and they also can't be proven alongside the
axioms because then the proofs just use the axioms. These limitations should
all be resolved in Verus relatively soon.

## Verifying

```sh
verus --crate-type=lib src/lib.rs
```
