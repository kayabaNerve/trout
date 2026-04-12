# Trout++ - Two Round Threshold ECDSA

Trout is a novel protocol implementing the first two-round multi-party ECDSA protocol for arbitrary
thresholds. Trout additionally benefits from every participant only having to broadcast an amount of
bytes independent to the set size, with the zero-knowledge proofs also having prover complexity
independent to the set size. This enables Trout to remain a low-bandwidth option even for large
signing sets (100+ nodes).

Trout++ extended Trout with support for preprocessing and with the security definitions necessary
to be composed with ROAST, completing a performant, robust, asynchronous service for threshold ECDSA
signing. It's further expanded with key derivation and broad support for importing existing keys.

Included in this repository is a Rust API for working with class groups with a subgroup where the
discrete-logarithm problem is easy, as posited within [CL15](https://eprint.iacr.org/2015/047).
Included are backends premised on [`gmp`](https://gmplib.org) via [`rug`](https://docs.rs/rug)
(requiring a C toolchain), [`malachite`](https://docs.rs/malachite) (offering a pure-Rust
variable-time option), and [`crypto-bigint`](https://docs.rs/crypto-bigint) (offering constant-time
options, believed to be the first of their kind for protocols which build upon CL15). These are not
claimed to be optimal, with [`BICYCL`](https://eprint.iacr.org/2022/1466) remaining the most
efficient option at this time.

Additionally included is the implementation of Trout++, as required to enable benchmarking. While
the implementation as written with good-practice in mind, it does not always propagate the
identification of faulty parties at this time (despite collecting and verifying the zero-knowledge
proofs as appropriate) and has not been audited. It is not in any way recommended or endorsed for
production use-cases at this time.

[Trout](https://eprint.iacr.org/2025/1666) was accepted to ACM CCS 2025. Its paper includes
benchmarks using `BICYCL` to facilitate proof verification and either `BICYCL` or the
`crypto-bigint` stack backend for proving (depending on whether discussing the numbers for the
variable-time or the constant-time prover).

Trout++ is expected to be published within the next few months, its benchmarks following the
commentary prior stated for Trout.

The libraries present in this repository have been improved since and may continue to be actively
updated.
