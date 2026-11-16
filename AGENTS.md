# Instructions for coding agents

These rules apply to every change in this repository. If `AGENTS.local.md`
exists next to this file, read it too and follow it; it holds local,
uncommitted instructions.

## Architecture

The Rust implementation in `rust/` is one crate. Its layering is enforced by
the dependency checker (`rust/src/bin/dependency_check`); keep the code and the
rules in `rust/src/bin/dependency_check/rules.txt` consistent with what follows.

### Compile time and run time

- Compile-time code never uses run-time code, and run-time code never uses
  compile-time code. Shared code uses neither. The dependency checker fixes
  each file's phase in its source (`phase` and `circuit_phase` in
  `rust/src/bin/dependency_check/main.rs`), not in `rules.txt`; a file it
  cannot classify fails the check, so classify a new kind of file there, in a
  reviewed change. The classes are:
  - compile time: `compile`, `mdoc::compile`, and the `circuit`, `allocate` and
    `fields` halves of each circuit in `circuits` and `mdoc::circuits`;
  - run time: `runtime`, `mdoc::runtime`, `mdoc::cbor` (native CBOR and mdoc
    parsing), and the `concrete` native-witness halves of circuits;
  - shared: `core`, `mdoc::proto`, `mdoc::testcases`, `util`, and the
    `constants`, `points` and `shape` halves of circuits (a `shape` is the
    witness layout: generic structs the circuit holds wires in and the native
    witness holds values in, with the one allocation and encoding order);
  - test-only bridges, which may use both: the `evaluate` halves of circuits,
    which turn native witnesses into circuit wires and must be declared only
    for tests;
  - neutral, which may use both: the binaries in `bin` and
    `mdoc::development_provider` (which compile and run), `mdoc::artifacts`
    (the stored circuit and proof files), and facades (`runtime`,
    `mdoc::circuits`, and each circuit's root module). A facade may contain
    only module declarations and `use`s; no item.

  A circuit half's submodules take the half's phase. Compile-time, run-time
  and shared code may not use neutral or bridge files. Tests may use both
  phases.
- Compile time and run time have separate field implementations. Do not share
  field arithmetic between them; each side implements its own, so that one can
  check the other. Reference implementations used as test oracles are
  `#[cfg(test)]`.
- `core` holds only what both sides must agree on:
  - `core::algebra`: the field and curve traits, `FieldID`, the canonical
    serialization of every field, and constants both sides must match (the
    Cantor basis, evaluation points, curve parameters). The generic EC point
    arithmetic is the one agreed exception.
  - `core::proto`: the compile/run-time contract: circuit formats and
    archives.

### Prover and verifier

- `runtime::v1::proto` and `runtime::v2::proto` are the prover/verifier
  contracts: proof formats and the public metadata both sides use. They may use
  only `core`, `util`, `runtime::algebra` and the transcript framing (v2) or
  subfield (v1), never a protocol implementation.
- Prover and verifier code stay separate; neither uses the other's files.
- The standalone prover and verifier build independently, with no compiler
  dependencies: `--no-default-features` with `prover` or `verifier` (plus
  `mdoc`, and `v1` for the deployed system), including the `prover_only` and
  `verifier_only` binaries, must not need the other role, the `compiler`
  feature, compile-time code, or the compiler's crates (`bumpalo`,
  `num-bigint`, `num-traits`, `rustc-hash`). Check with
  `cargo tree -e normal --no-default-features --features prover,mdoc,v1`
  (and the verifier and v2 equivalents).
- v1 and v2 are disjoint: no v1 file uses a v2 file or the reverse.
- v1 is the deployed system and is frozen. Do not break compatibility: its
  proof format, transcript, circuits and circuit IDs, parameters, public API
  and error codes stay as they are, and proofs must keep verifying across old
  and new builds in both directions. Change v1 only where the maintainer asks,
  and then only in ways that leave every byte it produces or accepts unchanged
  (for example a build fix); the v1 tests, test vectors and the
  `formal/lfzk-v1` inspectors must pass unchanged.

### Parameters

Parameter catalogs and tuning (for example the audited Polygero profiles) belong
to the offline tool `zk_tool`, which certifies them. The library stores only the
profiles an application chose (for example in `mdoc::proto`).

### Source layout and paths

- Module `foo` lives in `foo.rs`, its submodules in `foo/`, and its unit tests
  in `foo/tests.rs` or `foo/tests/`. Do not use `#[path]`. The exceptions are
  the double mount of `runtime/algebra/arch/generic.rs` from `arm.rs`, and
  the benches' `#[path = "support/memory.rs"]`, which shares the allocation
  tracker between bench targets.
- Every public item has exactly one public path. Implementation splits
  (`circuit`, `concrete`, `field`, `prover`, ...) are private modules behind
  their parent's `pub use`. Do not re-export another module's items, and do not
  rename on re-export; rename the definition instead.
- Name items through `use` imports rather than long inline `crate::` paths.
- Give items the narrowest visibility that works, but keep public types
  usable: a public type must be constructible or obtainable, readable, and
  nameable (no public type reachable only through a private module).

### Dependency rules

- The component rules must stay acyclic, and so must the file graph.
- A component with components below it owns only its root file; every other
  module needs its own rule.
- When the checker reports a new dependency, remove it, or, if it is intended,
  add it to `rules.txt` deliberately.
- The phase check and the prover/verifier contract check (`proto_allows`) are
  code, not rules; do not weaken them to make a change pass.

## Performance

- Do not accept performance regressions in the prover or the verifier. Measure
  hot-path changes (transcript, sumcheck, Polygero, packing) by interleaving
  runs of the parent and the change, pinned to one core; do not argue a
  regression away. Prefer designs that are free by construction.
- Memory consumption counts too: do not accept regressions in the prover's or
  the verifier's peak heap. Measure it with the benches' `bench-memory`
  feature, which reports each role's additional peak heap.
- Speedups must not depend on AVX2 or AVX-512. Measure AVX-free builds:
  `RUSTFLAGS="-C target-cpu=x86-64-v2 -C target-feature=+pclmulqdq"` with a
  separate `CARGO_TARGET_DIR`, run under
  `GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX,-AVX2,-AVX512F,-AVX512BW,-AVX512VL,-AVX512DQ,-AVX512CD,-AVX_Fast_Unaligned_Load`,
  and check that `objdump -d` shows no `%ymm` or `%zmm` registers.

## Code

- Do not develop tools in Python. Use Rust.
- Never use `OnceLock`. Pass explicitly owned initialization state instead.
- Tests live in their own files (see the layout above); library sources
  contain no inline `#[cfg(test)] mod tests { ... }`.
- Do not add clippy warnings; `cargo clippy --all-targets` must not report
  more than before the change.

## Formal development

- Lean proofs use only the standard axioms (`propext`, `Classical.choice`,
  `Quot.sound`): no `sorry`, no `native_decide` or other `ofReduceBool`
  routes. Kernel evaluation (`decide +kernel`) is fine. The one exception is
  the legacy numerical rows in the modules `LfzkV1` and `LfzkV1.*` and in
  `examples.Ligero.Longfellow.*`, which keep the documented native-evaluation
  allowance that `formal/scripts/Audit.lean` checks and reports separately.
  Nothing new may join it: `formal/scripts/audit.rs` rejects native
  evaluation in any other module, from the same list of roots.
- Lean must agree with Rust. After changes to circuits, parameters, or files
  the formal sources cite, run from `formal/` `lake build` and
  `lake build SecurityAudit`; from `rust/`
  `cargo run --release --features tooling --bin zk_tool -- certify-hahn --formal ../formal`
  and `... -- check-profiles --protocol polygero --check-lean ../formal`; and
  `formal/scripts/check_mdoc_round_shapes.rs` and the formal source audit
  `formal/scripts/audit.rs` (both built with `rustc --edition 2024 -O`);
  `precommit --formal` runs them all. Lean comments that name Rust files must
  follow file moves.

## Workflow

- Triage audit findings with the maintainer (fix, defer, or won't fix)
  before fixing them, stating each fix's prover cost.
- One logical change per commit, with a message that says what changed and
  why. Keep mechanical rewrites, formatting-only changes, and semantic edits
  in separate commits.
- Every commit passes all checks on its own; never rely on a later commit to
  fix the build, the tests, or the tooling, so history stays bisectable.
- Code outside `rust/` that builds against the crate must keep working:
  `formal/lfzk-v1/scripts` (`cargo build --release`, then run
  `inspect-v7-profile` and `inspect-v7-assertions`) and
  `formal/scripts/mdoc_round_shapes.rs` (through `check_mdoc_round_shapes`).

## Before every commit

From `rust/`, run the checklist runner:

```sh
cargo run --release --features tooling --bin precommit
```

It prints one line per step and stops at the first failing step
(`--keep-going` runs them all); each step's output is in
`target/precommit/<step>.log`, and `--help` lists the options. Its steps are:

1. `cargo +nightly fmt`, then
   `rustfmt +nightly --edition 2021 --config skip_children=true $(git ls-files 'src/*.rs' 'benches/*.rs')`
   (`cargo fmt` does not reach modules declared inside the `cfg_*!` macros).
2. The role and feature builds, warning-free: `cargo check --lib --bins
   --no-default-features` with each role and feature set, then the tests
   without mdoc (`--lib --tests --no-default-features --features
   testonly,tooling`), `--features testonly,tooling --tests --benches --bins`
   and `--all-targets`.
3. `cargo run --release --features tooling --bin dependency_check`
   (needs `rustup component add rust-analyzer`).
4. The standalone prover and verifier, v1 and v2, pull no compiler crate
   (`cargo tree -e normal --no-default-features`; see "Prover and verifier").
5. `cargo clippy --all-targets` reports no more warnings for any target than
   the base commit: `--base REV`, by default `HEAD` when the working tree has
   changes and `HEAD^` when it has none; or the counts given with
   `--clippy-counts`.
6. `cargo test --release --features testonly,tooling`, and the doctests on
   nightly, which also check `compile_fail` error codes:
   `cargo +nightly test --release --features testonly,tooling --doc`.
7. When architecture-specific code changes since the base (`runtime/algebra/arch`,
   limbs, `cfg(target_arch)`), or with `--cross`, the builds for every backend,
   since x86-64 does not compile the others: `--target aarch64-unknown-linux-gnu`,
   `--target armv7-unknown-linux-gnueabihf` with and without
   `--features arm-neon`, `--target i686-unknown-linux-gnu`, and the
   `force-generic-arch` and `limb32` features.
8. The code outside `rust/` that builds against the crate (see "Workflow"):
   the `formal/lfzk-v1/scripts` inspectors and `check_mdoc_round_shapes`.
9. With `--formal`, the formal checks of "Formal development": `lake build`,
   `lake build SecurityAudit`, `formal/scripts/audit.rs`, `certify-hahn` with
   a fresh cache, and `check-profiles`.
