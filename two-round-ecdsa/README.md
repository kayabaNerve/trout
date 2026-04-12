# 2-round Threshold ECDSA

This is an implementation of a simulatable 2-round threshold ECDSA protocol, for arbitrary
thresholds and support for preprocessing. It uses class groups as a Partially-Homomorphic Encryption
system, and is configurable to the number libraries/ZK proofs used. A constant-time backend is
available via `crypto-bigint`.

### Proofs

Only four relations in total are needed.

1) $R_{CL-EC}$: A proof a class-groups ciphertext encrypts the discrete logarithm of an EC point
2) $R_{ComKwlg}$: A proof of knowledge for the opening of a commitment over the class group
3) $R_{affCom}$: A proof of a transformation of a ciphertext by the opening of commitments

The first three are needed for `RoundOneProofs` to achieve unforgeability. The final proof is needed
by `RoundTwoProofs` only to achieve identifiable aborts. An implementation of `RoundOneProofs`,
`NoIdentifiableAborts`, is provided which does nothing to sacrifice identifiable aborts for
efficiency.

For the full set of proofs, Handong Cui, Kwan Yin Chan, Tsz Hon Yuen, Xin Kang, and Cheng-Kang Chu's
"Bandwidth-Efficient Zero-Knowledge Proofs for Threshold ECDSA" is preferred. These proofs do
require a hash-to-prime number, of which three implementations are provided in the codebase:

1) `CryptoPrimesStack`: A hash-to-prime internally using
   [`crypto-primes`](https://docs.rs/crypto-primes). This isn't safe per
   <https://github.com/entropyxyz/crypto-primes/issues/23> and
   <https://github.com/entropyxyz/crypto-primes/issues/25>. Additionally, this implementation may
   panic if too large a prime is requested (though `CryptoPrimesStackCcykc` is guaranteed to not
   panic with `Ccykc2023RoundOne` and `Ccykc2023RoundTwo`).
2) `CryptoPrimesHeap`: A hash-to-prime internally using
   [`crypto-primes`](https://docs.rs/crypto-primes), again unsafe per the prior reasons. It won't
   panic if too large a prime is requested though due to using a heap-allocated dynamically-sized
   integer instead of a stack-allocated fixed-sized integer. It is roughly twice as slow as
   `CryptoPrimesStack`.
3) `GmpPrimes`: A hash-to-prime internally using `gmp`'s `next_prime`. This is unsafe to use as it's
   biased to an unqualified degree. It is consistent across versions of `gmp`, ~4x faster than
   `CryptoPrimesStack`, and ~9x faster than `CryptoPrimesHeap`. It is the recommended choice.

### Future Work

Currently, elements of the class group are always of the class group with discriminant $\delta_p$.
Some elements can be left in the class group with discriminant $\delta_k$, shortening them ~10%.
Since such elements also would lack a subgroup component where the discrete-log problem is easy,
more efficient ZK proofs should exist for such elements (as CCYCK responses are of the form
$D \in \hat{G}, e \in Z$ where $e = (r + c * x) \mod ql$, where $q$ is the order of the subgroup and
$l$ is a randomly sampled prime. Simply $\mod l$ should be valid).
