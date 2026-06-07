# Trout

This repository contains the 'Trout-family' threshold signing protocols. All of
these protocols are consistent in intending to offer scalable and efficient
protocols for arbitrary thresholds, premised on class groups and worked on by
Hila Dahari-Garbian, Ariel Nof, and Luke Parker.

For the implementation of class groups underlying these protocols, please see the
[`class-groups` library](./class-groups).

Currently implemented is [Trout++](./two-round-ecdsa), a two-round ECDSA
signing protocol for arbitrary thresholds. Trout++ may be composed with
[ROAST](https://eprint.iacr.org/2022/550) to achieve a robust protocol over
asynchronous networks and supports a variety of desirable features such as
additive key derivation and optionally not requiring any additional setup.
