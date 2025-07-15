# Trout - Two Round Threshold ECDSA

Trout is a novel protocol implementing the first two-round multi-party ECDSA protocol for arbitrary
thresholds. Trout additionally benefits from every participant only having to broadcast an amount of
bytes independent to the set size, with the zero-knowledge proofs also having prover complexity
independent to the set size. This enables Trout to remain a low-bandwidth option even for large
signing sets (100+ nodes).

Included in this repository is a Rust API for working with class groups with a subgroup where the
discrete-logarithm problem is easy, as posited within [CL15](https://eprint.iacr.org/2015/047).
Included are backends premised on [`gmp`](https://gmplib.org) via [`rug`](https://docs.rs/rug)
(requiring a C toolchain), [`malachite`](https://docs.rs/malachite) (offering a pure-Rust
variable-time option), and [`crypto-bigint`](https://docs.rs/crypto-bigint) (offering constant-time
options, believed to be the first of their kind for protocols which build upon CL15). These are not
claimed to be optimal, with [`BICYCL`](https://eprint.iacr.org/2022/1466) remaining the most
efficient option at this time.

Additionally included is the implementation of Trout, as required to enable benchmarking. While the
implementation as written with good-practice in mind, it does not always propagate the
identification of faulty parties at this time (despite collecting and verifying the zero-knowledge
proofs as appropriate) and has not been audited. It is not in any way recommended or endorsed for
production use-cases at this time.

The Trout paper, including security proofs, has been accepted to a conference and is planned to
published on the IACR ePrint server shortly. Note the paper includes benchmarks using `BICYCL` to
facilitate proof verification and either `BICYCL` or the `crypto-bigint` stack backend for proving
(depending on whether discussing the numbers for the variable-time or the constant-time prover).

The libraries present in this repository have been improved since and may continue to be actively
updated.
