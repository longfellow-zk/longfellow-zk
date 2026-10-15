# Differencing Morton keys while preserving the existing traversal

Follow-up experiment, 2026-09-11. Same three circuits and IDs as [the component-template experiment](MORTON_REPORT.md); MLDSA-44 remains at period 6. No scheduler, wire, term, witness, or runtime-order changes.

## Result

**It compresses worse on all three fixtures.** Morton-key deltas use fewer bytes before compression with ULEB128, but lose repetition and produce substantially larger zstd output. This holds in both fixed-width and variable-width paired controls.

## Precisely what was tested

Keep every term in its existing canonical absolute Morton traversal. For each layer, start `previous_g = previous_M = previous_h0 = previous_h1 = 0`.

```
M(h0,h1) = spread_bits(h0) | (spread_bits(h1) << 1)

Coordinate record: (signed_delta(g), signed_delta(h0), signed_delta(h1), k)
Morton-key record: (signed_delta(g), M(h0,h1) - previous_M, k)
```

`h0` occupies even bit positions, `h1` odd positions, matching the actual runtime comparator. The key is calculated from the **absolute coordinates before subtraction**: this is not interleaving the old coordinate deltas. Key differences are unsigned because the existing traversal is monotone in `M`; every transition is checked. Coefficient indices and g deltas are held fixed. There is no sorting, component partitioning, local normalization, dictionary encoding, or template reuse in this experiment.

Two byte encodings:

- **Fixed 12 bytes/term:** old `(3,3,3,3)` versus new `(3,6,3)`. Both have equal raw size. Six-byte key differences suffice for these fixtures and are range-checked.
- **ULEB128:** variable-width unsigned integers, with LFC1's signed-delta convention for g and the old h deltas. This also tests the potential benefit of storing only three fields and nonnegative key gaps.

Both sides use the same experimental container, coefficient table, geometry, original ID, and traversal. The container's metadata layout differs from LFC1, and the LFC1 writer can remap coefficient indices. Thus the fixed-width coordinate control is not claimed to be byte-identical *as a file* to LFC1; the paired control, rather than stock LFC1, isolates the delta choice. Stock LFC1 numbers are included separately for context. All reported sizes include complete metadata and coefficients; no external compression dictionary is used.

## Complete sizes in bytes

| Circuit | Encoding | Raw | zstd-16 | zstd-22 |
|---|---|---:|---:|---:|
| mdoc signature | Stock LFC1 | 3,134,392 | 93,955 | 89,077 |
| | Coordinates, fixed 12 | 3,134,312 | 93,728 | 89,789 |
| | Morton key, fixed 12 | 3,134,312 | 156,065 | 148,107 |
| | Coordinates, ULEB128 | 1,123,658 | 84,190 | 79,177 |
| | Morton key, ULEB128 | 906,594 | 144,164 | 138,203 |
| mdoc hash | Stock LFC1 | 60,467,613 | 133,225 | 117,606 |
| | Coordinates, fixed 12 | 60,467,536 | 131,984 | 116,629 |
| | Morton key, fixed 12 | 60,467,536 | 224,264 | 197,689 |
| | Coordinates, ULEB128 | 22,699,530 | 113,724 | 104,553 |
| | Morton key, ULEB128 | 18,192,269 | 201,858 | 190,028 |
| MLDSA-44, period 6 | Stock LFC1 | 78,996,522 | 1,768,703 | 1,606,804 |
| | Coordinates, fixed 12 | 78,996,439 | 1,686,497 | 1,577,818 |
| | Morton key, fixed 12 | 78,996,439 | 3,127,033 | 2,851,148 |
| | Coordinates, ULEB128 | 28,889,924 | 1,521,036 | 1,430,368 |
| | Morton key, ULEB128 | 23,502,132 | 2,906,599 | 2,685,005 |

## Repetition measurements

Distinct full records include k; coordinate-only tuples omit it. Chunks are exact sequences of 32 full records, with identical boundaries on both sides. Incomplete layer tails are excluded only from the chunk statistic, never from the encoding.

| Circuit | Distinct records, coordinates → key | Distinct coordinate tuples → `(Δg,ΔM)` | Unique chunks, coordinates → key | Total chunks |
|---|---:|---:|---:|---:|
| mdoc signature | 14,192 → 25,066 | 12,022 → 21,982 | 4,489 → 5,570 | 8,101 |
| mdoc hash | 18,449 → 28,577 | 11,694 → 21,178 | 12,698 → 23,737 | 157,445 |
| MLDSA-44 | 174,923 → 368,451 | 150,766 → 330,936 | 74,793 → 86,111 | 205,640 |

## Why monotone keys need not be more compressible

Morton keys are monotone in the traversal, but their increments depend on absolute bit positions and carries. A simple example is the already-Morton-ordered sequence `(h0,h1) = (0,n)`:

```
n:          0  1  2  3  4
M(0,n):     0  2  8 10 32
Δh1:           1  1  1  1
ΔM:            2  6  2 22
```

The raw coordinate stride is constant, while the key gap varies and changes phase when translated. This demonstrates why replacing two signed coordinate deltas with one unsigned key gap need not preserve repeated delta records. The measured increases in distinct records and unique chunks are consistent with this loss of repetition. Fewer ULEB128 bytes per record do not compensate in zstd on these fixtures.

This is a state-dependent transform of consecutive **absolute points**, not an invertible function of a single old delta tuple: the same coordinate delta can produce several different key gaps. There is therefore no contradiction with cardinality preservation under invertible per-tuple transforms. Nor does this rule out every possible specialized code for Morton gaps; it rejects the straightforward fixed-width and ULEB128 encodings tested here.

## Correctness and load cost

All 12 circuit/encoding combinations passed three decode roundtrips. Decoding sums key gaps, deinterleaves the key into h0/h1, and reconstructs the original coordinate deltas **without sorting**. Every result has the original circuit ID and reserializes to byte-identical canonical LFC1. Proof geometry and proof inputs therefore remain unchanged; no new proof run was needed for this storage-only control.

Median of three warm runs, milliseconds, including zstd-16 decompression and ID hashing:

| Circuit | Coordinates fixed | Key fixed | Coordinates ULEB | Key ULEB |
|---|---:|---:|---:|---:|
| mdoc signature | 20.744 | 20.531 | 16.548 | 16.921 |
| mdoc hash | 350.610 | 336.562 | 263.041 | 264.495 |
| MLDSA-44 | 495.659 | 484.533 | 383.103 | 386.493 |

These are paired prototype decoder timings, not stock reader benchmarks. Other fixture runs overlapped, so small timing differences should not be interpreted as speed wins. The standalone decoder remains trusted-input experimental code, not a hardened production reader.

## Reproduction

```sh
MORTON_KEY_DELTAS_ONLY=1 cargo test -p mdoc-zk-circuits analyze_signature_morton -- --ignored --nocapture
MORTON_KEY_DELTAS_ONLY=1 cargo test -p mdoc-zk-circuits analyze_hash_morton -- --ignored --nocapture
MORTON_KEY_DELTAS_ONLY=1 cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
cargo test -p mdoc-zk-circuits morton_key::tests
```

Implementation: [morton_key.rs](morton_key.rs). Tests cover the interleave/deinterleave inverse, agreement with the actual Morton comparator over boundary values through 32-bit coordinates, and numeric encoding roundtrips through 64-bit values. Both unit tests pass in both mdoc test modules (four executions). Raw logs: [signature](results/morton-key-signature.log), [hash](results/morton-key-hash.log), [MLDSA](results/morton-key-mldsa.log).
