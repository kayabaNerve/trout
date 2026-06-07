# Class Groups

A library for working with binary quadratic forms as corresponding to elements
of a class group.

### Purpose

This library was specifically written to be used with respect to the
[CL15 framework](https://eprint.iacr.org/2025/047). It has a strong focus on
correctness however, clearly documenting what operations are supported within
which contexts, and is usable for working with primitive positive definite
binary quadratic forms of negative odd discriminant in general.

### Design Goals

This library is intended to be up to the standards required for deployment in a
production environment. Functions are documented with their technical
specification, allowing clear review and the development of alternative
implementations which remain compatible. This library is part of an ongoing
effort to submit a standard for the representation of and operations with
binary quadratic forms. This includes a complete wire specification for the
encoding of (un)compressed binary forms and a specification for sampling binary
quadratic forms from the class group.

The included [`CryptoBigintElement`] is a constant-time backend which is
intended to stand up to intense scrutiny (with extensive documentation on each
intermediary term to prove their correct calculation within the declared
bounds) and also be eligible for use with sensitive data such as private keys
(which would be at risk of being leaked via timing analysis if used with a
variable-time representation of group elements). The library is modular to the
backend however and [`bicycl`](https://docs.rs/bicycl) offers a highly
efficient variable-time backend. Please review its documentation for more
information and the associated disclaimers.

This library supports no-`std` and even no-`alloc`, allowing deployment in
constrained environments with statically-defined (bounded) memory.

### Status

This library is actively being worked on to evolve from a research proof of
concept to such standards, though much progress has been made. It is not yet
ready for production use and has not received any external review at this time.
