# Current mdoc dual-order benchmark

Current experimental v8, two disclosed attributes, same existing LFC2 circuits
for both schedules. Release build, allocator instrumentation from the existing
mdoc_zk_bench_current benchmark. Three alternating process runs per mode, 10
Criterion samples per phase per run, 1-second warmup and 3-second target
measurement (automatically extended when needed).

## Results

Times are medians of the three Criterion point estimates. Prove includes
decompression, input/witness preparation, both commitments, both proofs, and
serialization. Verify includes decompression and proof parsing. Compilation is
outside timing and phase heap measurements.

| Mode | Prove ms | Verify ms | Prover peak additional heap bytes | Verifier peak additional heap bytes | Proof bytes |
|---|---:|---:|---:|---:|---:|
| Hand-major (default) | 392.02 | 201.69 | 96768982 | 39350856 | 344236 |
| Round-major (internal Morton sort) | 752.82 | 201.04 | 120644950 | 39350696 | 344076 |

Individual time estimates (prove / verify ms):

- Hand-major: 393.17 / 201.69; 386.48 / 198.49; 392.02 / 201.71.
- Round-major: 751.82 / 201.04; 758.10 / 199.49; 752.82 / 201.05.

Heap and proof sizes were identical across repetitions of each mode. Proof
geometry is the same; changing the transcript changes Merkle openings, allowing
small serialized proof-length differences. All dry-run and timed verifier calls
succeeded.

## Circuit sizes (identical in both modes)

- Segmented archive without zstd: 770782 bytes.
- Archive with zstd level 16: 183465 bytes.
- Hash: 3396148 non-input wires, 6394835 terms, 20 layers.
- Signature: 179677 non-input wires, 276481 terms, 21 layers.
- Combined ID: 4bba6d33dd704c8b54aa51206203ad4b7f6db7d2d3e5c4e4e0be8eea774e2198.

Peak additional heap is live Rust allocator memory above the phase-entry
baseline, not RSS. Whole-process RSS high-water marks were 1822332–1822956 KiB,
dominated by compiling the circuits at startup, and are not prover/verifier
working-memory measurements.

## Reproduction and scope

No repository source was modified. This temporary crate snapshots the current
mdoc benchmark and application prover/verifier wrappers. The wrappers use the
original runtime library APIs; only their explicit sumcheck-order selection is
overridden by MDOC_SUMCHECK_ORDER. The v8 spec, input rules, compiler, circuits,
wire numbering, and runtime kernels are unchanged. src/main.rs contains the
benchmark and allocator; src/prover.rs and src/verifier.rs contain the wrappers.

Build:
```sh
cargo build --release --offline --manifest-path /tmp/mdoc-dual-bench.qFvFhT/Cargo.toml --target-dir /home/athena/sandbox/longfellow-zk/rust/target
```

Run from this directory, replacing hand-major with round-major:
```sh
MDOC_SUMCHECK_ORDER=hand-major /home/athena/sandbox/longfellow-zk/rust/target/release/mdoc-dual-bench --bench --noplot --measurement-time 3 --warm-up-time 1
```

Raw logs: hand-major-{1,2,3}.log and round-major-{1,2,3}.log in this directory.
Criterion's automatic change percentages compare successive different modes;
the absolute time estimates above are the relevant results.
