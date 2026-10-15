# Sorted canonical circuit ID experiment

## Implementation

Added `core_proto::circuit::compute_canonical_id(f, raw)`. The existing
`compute_id` body is unchanged, as are its reader/compiler/prover/verifier
call sites and all stored circuit IDs. The new function is opt-in and does not
mutate the circuit.

For each layer it expands absolute coordinates into 16-byte records
`[g, h0, h1, coefficient_index]`, sorts them lexicographically by
`(g, h0, h1, coefficient_bytes)`, then feeds the existing term byte encoding
into SHA-256. Coefficient bytes are cached once per constant, not allocated per
term. Sorting uses Rust's unstable comparison sort; no radix sort or hash table.

The header, per-layer geometry/term count, and coordinate/coefficient encoding
are exactly those of the existing ID. Thus the canonical ID equals the old ID
of an explicitly canonically sorted circuit. There is no new hash-domain prefix:
this is the existing circuit encoding in a canonical traversal, exposed through
a separate API.

Invariance covers term permutations within each layer, constant-table numbering,
unused constants, and LFC1/LFC2 segmentation. Duplicates and zero-coefficient
assertion markers are preserved. It does not identify circuits under wire
renaming, swapping input hands, reordering layers, combining coefficients, or
other algebraic transformations.

## Method

Measured on 2026-09-12, Linux x86-64, AMD Ryzen 9 9950X, Rust 1.97.1,
release build with the workspace's `-C target-cpu=native`.

All inputs are the existing saved
`target/traversal-circuits/{dataset}--kind_abs_lex0213_r5.lfc2` files.
MLDSA uses period 6. This compares both ID functions on precisely the same
immutable circuit layout, not a regenerated or differently scheduled circuit.

Timing is ID computation only: decoding, disk reads, benchmark output, and the
final legacy-ID/non-mutation check are excluded. Each method is warmed once;
execution order alternates over nine repetitions, with medians reported.
Timing uses the system allocator without heap instrumentation. No proof
generation is included.

Allocation measurements use separate fresh processes with the tracking
allocator, one selected method and one invocation, without warmup. Reported
additional heap is measured maximum live requested allocation above the
already-loaded circuit baseline, not a formula or vector-capacity estimate.
It includes serialized constants and the sorting vector; it excludes the
8 KiB stack buffer, allocator overhead, and the preexisting circuit.

RSS is separately read from Linux `/proc/self/status` (VmRSS/VmHWM).
The single-invocation table reports the process high-water mark after hashing,
including the loaded circuit, runtime, allocator pages, and any earlier loader
peak. It is not an incremental heap measurement. GNU time's max RSS is also
preserved in the raw log; small differences from procfs readings occur.

## ID runtime

| Circuit | Current ms | Canonical ms | Ratio |
|---|---:|---:|---:|
| mdoc hash, 1 attr | 131.66 | 291.60 | 2.21× |
| mdoc hash, 2 attrs | 140.91 | 310.83 | 2.21× |
| mdoc hash, 3 attrs | 147.21 | 327.16 | 2.22× |
| mdoc hash, 4 attrs | 155.01 | 346.23 | 2.23× |
| mdoc signature | 8.30 | 13.65 | 1.64× |
| MLDSA-44 | 173.05 | 312.04 | 1.80× |
| MLDSA-65 | 208.85 | 384.77 | 1.84× |

For the two-attribute mdoc pair, summing the hash and signature medians gives
149.21 ms current versus 324.49 ms canonical, an extra 175.28 ms per pair of ID
computations. This is an ID-only comparison, not a newly measured prover or
verifier benchmark. Since the new function is not wired into those paths, their
current behavior is unchanged.

## Measured peak memory, one invocation per fresh process

| Circuit | Current extra heap bytes | Canonical extra heap bytes | Canonical extra heap MiB | Current process peak RSS MiB | Canonical process peak RSS MiB |
|---|---:|---:|---:|---:|---:|
| mdoc hash, 1 attr | 12,640 | 41,194,400 | 39.29 | 4.69 | 43.93 |
| mdoc hash, 2 attrs | 12,640 | 43,396,720 | 41.39 | 4.75 | 46.46 |
| mdoc hash, 3 attrs | 12,640 | 45,599,040 | 43.49 | 4.94 | 48.46 |
| mdoc hash, 4 attrs | 12,640 | 47,801,360 | 45.59 | 4.94 | 50.48 |
| mdoc signature | 34,720 | 740,848 | 0.71 | 3.69 | 4.32 |
| MLDSA-44 | 53,376 | 36,339,280 | 34.66 | 12.94 | 48.27 |
| MLDSA-65 | 53,760 | 55,773,824 | 53.19 | 13.94 | 68.00 |

The measured heap increase matches one 16-byte record per term of the largest
layer: mdoc hash2 has 2,711,505 terms in that layer, MLDSA-44 has 2,267,869,
and MLDSA-65 has 3,482,504. The current function only materializes serialized
constants and streams terms. The canonical function additionally materializes
one full layer. The sort buffer is freed before the next layer is allocated.

## Repeated-call RSS

Separate uninstrumented processes, nine successive calls to only one method
per process (no warmup). This exposes allocator retention that live-allocation
counts do not capture. The method's temporary vectors are dropped after each
call, but the allocator can keep their pages mapped/resident.

| Circuit | Current peak RSS MiB | Canonical peak RSS MiB | Canonical RSS before MiB | Canonical RSS after MiB |
|---|---:|---:|---:|---:|
| mdoc hash, 2 attrs | 4.92 | 58.81 | 4.77 | 18.41 |
| mdoc signature | 3.73 | 4.43 | 3.68 | 4.43 |
| MLDSA-44 | 13.17 | 50.57 | 11.06 | 16.39 |
| MLDSA-65 | 13.92 | 70.35 | 11.65 | 17.95 |

In particular, canonical mdoc hash2 reaches roughly 59 MiB process RSS after
repeated calls rather than the roughly 46 MiB fresh-call peak. This is why the
additional-live-heap figures alone are not a complete resident-memory budget.

## Validation

- Canonical invariance tested for prime and binary fields: permutations,
  duplicate coefficients at distinct table indices, table renumbering, unused
  constants, LFC1/LFC2 serialization, segmentation, duplicates, and assertions.
- IDs change for changed coordinates/coefficient markers, removed duplicates,
  changed geometry, or changed layer order.
- Independent reference checks compare against the original stream ID over an
  explicitly sorted circuit, including empty layers/circuits and hash-buffer
  boundaries.
- All seven benchmark datasets retain their original stored ID after canonical
  hashing; canonical outputs are stable across all repetitions and build modes.
- Core-proto, sumcheck, and ZK tests: 35 passed, including the legacy RFC vector.
- Workspace all-target checking and strict core-proto Clippy passed.
- Strict Clippy for the benchmark target with `--no-deps` passed.
- No stored circuit, segmentation, proof size, challenge schedule, or protocol
  ID computation changed.

## Reproduce

Timing (repeat for each dataset):

```sh
CID_DATASET=mdoc_hash2 cargo test -p circuits-experimental --release --test canonical_id_bench -- --ignored --nocapture --test-threads=1
```

Memory, each command launches a fresh test process:

```sh
CID_DATASET=mdoc_hash2 CID_METHOD=current CID_REPEATS=1 cargo test -p circuits-experimental --release --features bench-memory --test canonical_id_bench -- --ignored --nocapture --test-threads=1
CID_DATASET=mdoc_hash2 CID_METHOD=canonical CID_REPEATS=1 cargo test -p circuits-experimental --release --features bench-memory --test canonical_id_bench -- --ignored --nocapture --test-threads=1
```

Repeated-call RSS: omit `bench-memory`, select one `CID_METHOD`, and set
`CID_REPEATS=9`. Dataset choices are mdoc_hash1 through mdoc_hash4, mdoc_sig,
mldsa44, and mldsa65. `CID_CIRCUIT_DIR` overrides the saved-circuit directory.

Artifacts: [timing](results/canonical-id-timing.log),
[allocation and fresh-process RSS](results/canonical-id-memory.log),
[repeated-call RSS](results/canonical-id-repeated.log),
[CSV](results/canonical-id.csv). All hashes and raw samples are in the logs.

## Conclusion

Canonical sorting is straightforward and leaves protocol behavior untouched,
but costs 1.6–2.2× the ID runtime on these layouts and tens of MiB for large
layers. It should not silently replace the streaming ID in per-proof load or
verification paths. Callers can explicitly compute/cache it where an
order-independent identity is useful.
