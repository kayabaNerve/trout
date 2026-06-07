# BICYCL

Rust bindings to [BICYCL](https://gite.lirmm.fr/crypto/bicycl/-/tree/master).

This library explicitly provides bindings not for the entirety of BICYCL, but
for the subset necessary to fulfill the
[`class-groups` API](https://docs.rs/class-groups).

These bindings are not written, maintained, or endorsed by the authors of
BICYCL. BICYCL is licensed under the GPL-3.0 and was written by Cyril Bouvier,
Guilhem Castagnos, Laurent Imbert, Fabien Laguillaumie and Quentin Combal.

### Building

The library requires three dependencies to be built:
- `git`, to retrieve a copy of BICYCL
- `c++`, to compile BICYCL
- `gmp, gmpxx` as libraries on the system

### Safety

These bindings have received any external review at this time. Additionally,
the BICYCL library offers the following disclaimer over itself:

> The BICYCL library is a research project and is not production-ready.
> In particular, the secret-dependent primitives are not constant-time and may be vulnerable to various kind of well known side-channel attacks.
> It should not be used in real cryptographic projects.

https://gite.lirmm.fr/crypto/bicycl/-/blob/cd4fd367759e4bd9f0ee466b3ca59782b28332af/README.md?plain=1#L2-L4

This library is not to be considered safe for usage in any context and may be
`unsafe` according to Rust, with undefined behavior.
