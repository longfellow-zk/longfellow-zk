# Dual packing naming validation, 2026-10-27

The standalone protocol is `runtime::dual_packing`, with its codec in
`runtime::proto::dual_packing` and sources in `runtime/dual-packing`.
Public proof/mask types are `DualPacking128Proof` and
`DualPackingMaskValues`. Constants use `DUAL_PACKING_`, and the packed
composition exposes `dual_packing_proof` and `dual_packing_start`.
Documentation, test names, dependency registries, error messages, profiler
labels and recorded benchmark phase keys use the same terminology.

The transcript domain is `longfellow/dual-packing128/flat-trace/v1`.
Updating that domain changes experimental v9 proof bytes. Algebra,
serialization field order, message counts and commitment geometry are
unchanged. Earlier benchmark timings and fingerprints retain their
historical values; this report records the current proof check.

With the existing two-attribute compact-v9 cache and DeterministicRng(42),
the fresh proof verifies and has 185,332 bytes, SHA256:

```text
503b42b3bde162e79bf3ff1404189c179caa2e6a4d433cf61e003054a52cf6ed
```

The earlier-domain golden proof is rejected. The small proof-length change
comes from different Fiat-Shamir opening queries in the unchanged backend.

Validation passed:

- `cargo test --lib --features experimental dual_packing`: 10 tests.
- Packed commitment end-to-end and adversarial test: passed.
- Dependency and source-layout checks: 21 tests.
- Full v9 application test: all three compiler variants, two and four
  attributes, cache round trips and Boolean-window proof equality.
- Prover, verifier, compiler and data feature builds with `experimental,mdoc`.
- All-target Clippy with `testonly,experimental,bench-profile,bench-memory`;
  only existing warnings remain.
- Release v9 benchmark target builds; fresh proof generation, verification
  and prior-domain proof rejection were checked independently.
- Nightly rustfmt, whitespace checks, and repository content/filename scans.

Raw test/build evidence is in [protocol-tests.log](protocol-tests.log) and
[integration.log](integration.log). This naming update changes no formal
sources or security claims.
