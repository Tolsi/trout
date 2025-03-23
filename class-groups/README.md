# Class Groups

A library for working with class groups which have a subgroup where the discrete logarithm problem
is easy.

This library supports modular backends in order to enable evaluation of different backends for
performance, and to enable a constant-time backend for secret-sensitive operations.

Currently provided are the following backends:
- `MalachiteElement`: An implementation which uses `malachite`, a pure-Rust integer library.
- `GmpElement`: An implementation which uses `gmp`. This is 20-30% faster than `MalachiteElement`.

`ClassGroup`s cannot be serialized and *SHOULD* be saved as the entropy used for a seeded RNG which
creates them (such as `rand_chacha::ChaCha20Rng`). This same premise also allows creating the same
class group over distinct backends, as `ClassGroup::setup` will yield the same class group
*regardless* of backend chosen.

Compression of elements is implemented as described in <https://eprint.iacr.org/2020/196>, with
slight changes for how `f` is derived from `g`. The decompression algorithm asserts the compressed
representation was canonical.
