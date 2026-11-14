# Instructions for coding agents

These rules apply to every change in this repository. If `AGENTS.local.md`
exists next to this file, read it too and follow it; it holds local,
uncommitted instructions.

## Architecture

The Rust implementation in `rust/` is one crate. Its layering is enforced by
the dependency checker (`rust/src/bin/dependency_check`); keep the code and the
rules in `rust/src/bin/dependency_check/rules.txt` consistent with what follows.

### Compile time and run time

- Compile-time code (`compile`, `mdoc::compile`, the circuit halves of
  `circuits`) never uses run-time code (`runtime`, `mdoc::runtime`, the
  `concrete` native-witness halves of `circuits`), and run-time code never uses
  compile-time code. Tests may use both.
- Compile time and run time have separate field implementations. Do not share
  field arithmetic between them; each side implements its own, so that one can
  check the other. Reference implementations used as test oracles are
  `#[cfg(test)]`.
- `core` holds only what both sides must agree on:
  - `core::algebra`: the field and curve traits, `FieldID`, the canonical
    serialization of every field, and constants both sides must match (the
    Cantor basis, evaluation points, curve parameters). The generic EC point
    arithmetic is the one agreed exception.
  - `core::proto`: the compile/run-time contract: circuit formats, archives,
    and the parameter types a specification carries (for example the Polygero
    dimensions).

### Prover and verifier

- `runtime::v1::proto` and `runtime::v2::proto` are the prover/verifier
  contracts: proof formats and the public metadata both sides use. They may use
  only `core`, `runtime::algebra` and the transcript framing (v2) or subfield
  (v1), never a protocol implementation.
- Prover and verifier code stay separate; neither uses the other's files.
- v1 and v2 are disjoint: no v1 file uses a v2 file or the reverse.

### Parameters

Parameter catalogs and tuning (for example the audited Polygero profiles) belong
to the offline tool `zk_tool`, which certifies them. The library stores only the
profiles an application chose (for example in `mdoc::proto`).

### Source layout and paths

- Module `foo` lives in `foo.rs`, its submodules in `foo/`, and its unit tests
  in `foo/tests.rs` or `foo/tests/`. Do not use `#[path]` (the double mount of
  `runtime/algebra/arch/generic.rs` from `arm.rs` is the one exception).
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

## Performance

- Do not accept performance regressions in the prover or the verifier. Measure
  hot-path changes (transcript, sumcheck, Polygero, packing) by interleaving
  runs of the parent and the change, pinned to one core; do not argue a
  regression away. Prefer designs that are free by construction.
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
  routes. Kernel evaluation (`decide +kernel`) is fine.
- Lean must agree with Rust. After changes to circuits, parameters, or files
  the formal sources cite, run from `formal/` `lake build` and
  `lake build SecurityAudit`; from `rust/`
  `cargo run --release --features tooling --bin zk_tool -- certify-hahn --formal ../formal`
  and `... -- check-profiles --protocol polygero --check-lean ../formal`; and
  `formal/scripts/check_mdoc_round_shapes.rs` and the formal source audit
  `formal/scripts/audit.rs` (both built with `rustc --edition 2024 -O`). Lean
  comments that name Rust files must follow file moves.

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

From `rust/`:

1. `cargo +nightly fmt`, then
   `rustfmt +nightly --edition 2021 --config skip_children=true $(git ls-files 'src/*.rs' 'benches/*.rs')`
   (`cargo fmt` does not reach modules declared inside the `cfg_*!` macros).
2. `cargo run --release --features tooling --bin dependency_check`
   (needs `rustup component add rust-analyzer`).
3. The role and feature builds from `.github/workflows/production_ci.yml`,
   warning-free. When architecture-specific code changes (`runtime/algebra/arch`,
   limbs, `cfg(target_arch)`), also build for every backend, since x86-64 does
   not compile the others: `--target aarch64-unknown-linux-gnu`,
   `--target armv7-unknown-linux-gnueabihf` with and without
   `--features arm-neon`, `--target i686-unknown-linux-gnu`, and the
   `force-generic-arch` and `limb32` features.
4. `cargo test --release --features testonly,tooling`, and the doctests on
   nightly, which also check `compile_fail` error codes:
   `cargo +nightly test --release --features testonly,tooling --doc`.
