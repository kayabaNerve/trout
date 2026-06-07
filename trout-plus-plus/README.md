# Two-Round Threshold ECDSA (Trout)

This is an implementation of Trout++, a two-round threshold signing protocol
for ECDSA signatures. Trout++ boasts many desired features, including:

- O(1) per-participant broadcast
- O(n) per-participant computation

These two properties allow Trout++ to scale from small signing sets (2-of-3) to
even massive signing sets (667-of-1000).

- Two rounds
- Identifiable aborts
- Message- (and signing-set-) independent first round

These properties ensure Trout++ is able to compose with
[ROAST](https://eprint.iacr.org/2022/550) to become a _robust_ protocol even
over _asynchronous networks_.

Additionally, Trout++ supports _additive key derivation_. With two
Shamir-secret-shared keys, it is possible to derive _multiple signing keys_
from these base keys without performing additional key generation protocols.

Finally, Trout++ supports all of this with _no additional setup_. This is by,
on paper, virtue of having a one-round setup which can be run
_in parallel with the first round of the signing protocol_. This avoids having
to perform, and store, a Trout++-specific setup in exchange for increasing the
cost of the signing protocol by a constant factor (so while maintaining all of
the advertised complexities and functionalities).

Trout++ is proven secure for static adversaries and arbitrary thresholds (and
remains composable with ROAST, ensuring output delivery, even for arbitrary
thresholds).

### Additively-Homomorphic Encryption

Trout++ makes use of an unknown-order group with a known-order subgroup where
the discrete-log problem is easy. While an RSA moduli would (in theory) work to
this end, as presented within the Paillier cryptosystem, Trout++ makes use of
class groups as presented by the
[CL15 cryptosystem](https://eprint.iacr.org/2015/047). This enables a
_transparent setup_* (as the entire group must use the same unknown-order
group) and offers a message space corresponding to the scalar field of our
elliptic curve (removing the need for range proofs or anything approximate).

Class groups have been subject to less review compared to RSA moduli as unknown
order groups. This library makes no suggestion or implication class groups, as
used by Trout++, are fit for cryptographic usage (despite implementing a
library only desirable for usage if that condition is true).

*While there are
[multi-party protocols for RSA moduli](https://eprint.iacr.org/2023/998), they
remain quite complex with only statistical bounds for their termination.
Alternatively, as we do not require knowing the order of the unknown-order
group, we could sample an RSA modulus of unknown factorization although these
would be quite large and multiple orders of magnitude larger than desired.

### Assumptions

The following is a layman's overview of the assumptions relied upon by the
Trout++ protocol.

- ECDSA signatures are secure to begin with
- The Hard Subgroup Membership (HSM) assumption
  (as presented in https://eprint.iacr.org/2018/791), stating it's hard to
  distinguish an element of the class group without a term from the known-order
  subgroup
- The Adaptive Root Assumption, stating it's hard to find an odd prime root of
  an element in the class group when challenged to do so

We believe these to be conservative assumptions, as justified when working
within this framework. We also note tighter reductions MAY be possible
regarding the usage of the HSM assumption, though we do not include such proofs
at this time.

For the exact zero-knowledge proofs, Trout++ uses a composition/derivative of
the proofs presented in
Bandwidth-Efficient Zero-Knowledge Proofs for Threshold ECDSA by
Handong Cui, Kwan Yin Chan, Tsz Hon Yuen, Xin Kang, and Cheng-Kang Chu.
Please refer to the [original Trout paper](https://eprint.iacr.org/2025/1666)'s
Appendix A for the generalization to arbitrary statements. Proofs _MAY_ be
omitted from the second round to trade identifiable aborts for reduced
bandwidth and better performance.

### Implementation

This implementation of Trout++ is built over the
[`class-groups`](https://docs.rs/class-groups) library. This offers technical
specifications for the representation of and operations over the class group,
while also allowing modularity to the literal implementation. The
`class-groups` library itself offers a
[constant-time implementation](
  https://docs.rs/class-groups/latest/class_groups/crypto_bigint/element/struct.CryptoBigintElement.html
)
built on top of [`crypto-bigint`](https://docs.rs/crypto-bigint), as amenable
for usage with secrets, yet there also exist
[bindings to BICYCL](https://docs.rs/bicycl) for a much more efficient
(variable-time, not viable for usage with secrets) implementation. This library
propagates this forward by separately designating the _prover's_ type for
representing elements of the class group (which will be used with secrets) from
the _verifier's_ type for representing elements of the class group (which will
not be used with secrets). This allows limiting constant-time implementations,
which are slower, to solely when secrets are being worked with.

`class-groups`, BICYCL, the bindings to BICYCL, and this implementation of
Trout++ have not been externally reviewed or audited as far as the authors of
this implementation are aware. Please carefully read and consider all security
implications for each library used.

Trout++ is explicitly presented as composable with ROAST and is intended to be
deployed in conjunction with ROAST when used with non-ideal networks (such as
every real network). Despite this, this implementation of Trout++ only
implements the core signing protocol itself and defers the implementation of
ROAST to the caller.

### Specification

The `class-groups` library contains a
[specification for encoding elements](
  https://docs.rs/class-groups/latest/class_groups/crypto_bigint/encoding/index.html
). Trout++ is expected to continue with an exact technical specification though
this is still a work in progress.

### History

Trout's design began in December, 2023 with sketches (and an experimental
implementation) of a two-round threshold ECDSA publicly posted in
January, 2024. Trout was improved, proven, and published by
Hila Dahari-Garbian, Ariel Nof, and Luke Parker in ACM CCS 2025. This
repository was cited as containing the experimental implementation of Trout but
it has since been improved and updated to Trout++. The history is available via
Git however.

Trout++ continued with an optimized commitment scheme and focusing on features,
in order to attempt to become a definitive choice for threshold ECDSA.
Composition with ROAST was also an explicit goal in order to clearly provide a
path forward to practical deployment without simply assuming an ideal network.
Trout++'s paper was submitted to a conference and is expected to be publicly
available soon.
