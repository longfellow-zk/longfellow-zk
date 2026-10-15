# Longfellow ZK (Rust Implementation)

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](../LICENSE)
[![IETF Draft](https://img.shields.io/badge/IETF%20Draft-draft--google--cfrg--libzk-lightgrey)](https://datatracker.ietf.org/doc/draft-google-cfrg-libzk/)

This directory contains the Rust implementation of the Longfellow
Zero-Knowledge (ZK) proof system. It remains under development.

The major problem with the C++ implementation was the confusing
organization of circuits.  We believe that this implementation is a
major improvement on this front.  We have reworked all circuits in
units with cleanly defined interfaces and extensive tests.  The Rust
type system helps with keeping circuits well-structured and organized,
as opposed to the old C++ templates.  The new compiler supports
rudimentary debug symbols so that one can assert that an invalid input
triggers the exact assertion that is expected to catch that case (as
opposed to a generic "some assertion has failed" of the old system).

All circuits, but especially the mdoc-zk circuits, have been reworked
to be much more stringent.  They perform paranoid checks on all
inputs, irrespective of whether they are necessary or not.  We have
organized the code to maximize local auditability as opposed to
circuit size.

In the original comparison with the C++ compiler, the full mdoc-zk
circuits were about 10% smaller despite performing more checks.

We have also rewritten the runtime portion (the prover and verifier)
in Rust. In the measurements behind this rewrite, performance was
comparable to the C++ implementation and the Rust prover used less than
100MB to produce a proof for the full mdoc-zk circuits, versus about
170MB for the then-current C++ prover and about 600MB for the initial
2025 prover. These are historical measurements, not current guarantees.

We have defined a circuit format called LFC2 that is more compact than
the C++ format (retroactively named LFC1). In the original mdoc-zk
comparison, LFC2 circuits occupied about 1MB before zstd compression,
versus about 100MB for LFC1.

The implementation includes an LFC1 reader to support the C++ circuit
format. Its intended compatibility includes bit-for-bit equal proofs
for matching circuits and prover randomness.

We are also switching to a new development model.  In the past, the
source of truth was an internal Google repository, with periodic
pushes to github from us (Google).  Going forward, the source of truth
will be github and Google will periodically import github as needed.
This switch will make it easier for us to accept third-party
contributions.

The older C++ implementation remains in [`../lib`](../lib); this Rust
workspace does not contain a separate C++ runtime for its new circuits.

---

## Building and Testing

### Requirements
A current stable Rust toolchain.

### Build the Workspace
```bash
cargo build --release
```

### Run Tests
To run all unit and integration tests across all workspace crates in release mode:
```bash
cargo test -r
```

### Run Benchmarks
To run the end-to-end mDOC ZK performance benchmarks:
```bash
cargo bench -p mdoc-zk-runtime
```

---

## License

Licensed under the Apache License, Version 2.0. See [LICENSE](../LICENSE) for details.
