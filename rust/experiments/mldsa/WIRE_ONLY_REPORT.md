# Wire renaming with fixed inputs and unchanged global Morton order

## Outcome

No 500,000-byte solution was found. The production scheduler, LFC2 format, segmenter, decoder, prover and verifier were not changed in this investigation. Existing unrelated/preexisting workspace changes were preserved.

73 deterministic layout policies (including baseline, with some duplicate layouts) were screened on each of mdoc signature, mdoc hash and MLDSA44 period 6. This is a finite heuristic search, not an exhaustive enumeration of factorially many permutations. All 219 cases passed exact inverse-renaming and fixed-input checks. Five policies received LFC1/native-LFC2/segmented-LFC2 zstd-16 and zstd-22 measurements on all three fixtures.

The previous approximately 528 kB result used non-Morton term traversal and is **ineligible** under the current constraints. Private-input reordering and segmentation-window sweeps are also ineligible and were stopped. None is included in these results.

## Contract enforced by the experiment

- Every original circuit input ID is fixed, including public inputs, private witnesses, and constant input wire 0.
- External output IDs are fixed as well.
- Only intermediate wire IDs are permuted; no extra wires, padding, witnesses, terms, or layers.
- The same permutation is applied to a layer's outputs and the next layer's references to them. The inverse must recover the original ordered term lists exactly.
- Multiplicands are canonically oriented and every stored layer is globally Morton-sorted, then ordered by output ID and semantic coefficient bytes. No decoder-side sorting or remapping.
- The first layer's entire ordered input-pair stream must remain unchanged. Renaming its outputs can change g and ties, but cannot change the Morton order of its fixed h0/h1 pairs.
- The production segmenter remains unchanged (window 32). The wire-only runner rejects traversal and window override options.

Consequently, layers cannot be optimized independently: changing a wire ID changes both an output coordinate in one layer and input coordinates in its consumer layer. This is a concrete constraint on component packing, not just an encoding detail.

## Main comparison

Segmented LFC2, compressed at zstd-22, bytes:

| Shared policy | mdoc signature | mdoc hash | MLDSA44 |
|---|---:|---:|---:|
| Baseline | 117854 | 161848 | 2091823 |
| Move internal copies of 1 to the end | 110995 | 157358 | 2090479 |
| Swap internal copies of 1 with end positions | 111650 | 159039 | 2090699 |
| Reverse nonconstant intermediate wire order, constants first | 112475 | 161897 | 2066780 |
| Whole-component packing, exact fan-in ordering | 102311 | 1693065 | 1173062 |

The last policy yields a substantial MLDSA reduction, but increases mdoc hash by over 10x. It is rejected as a shared policy. Reversal has only a small MLDSA gain and a small hash regression. Constant-last is a small shared improvement, not an answer to the MLDSA size problem. It remains an opt-in experiment, not an adopted production scheduler.

The larger sweep includes per-layer components both including and excluding every known copy of 1; minimum-ID component ordering; old/reverse/degree/first/last/fan-in/shape/min-max/Morton/barycenter/median producer ordering; repeated forward/backward consumer sweeps; whole-circuit components excluding original inputs and constant-only wires; five constant-placement positions plus swaps; and low-bit rotations, reversals and complements in complete aligned power-of-two blocks. Fixed inputs and partial tails are unchanged for bit permutations.

See [all raw/compressed sizes, delta counts and memory metrics](WIRE_ONLY_DATA.md).

## What the measurements establish

1. Component contiguity alone is insufficient. Whole-component fan-in numbering decreases MLDSA's global distinct deltas from 174923 to 108266, while increasing mdoc hash from 18449 to 514636. The term counts and circuits' algebra are identical. Producer-local ordering can destroy the consumer-side difference patterns which made the original hash layout compact.
2. Constant-copy position is not the principal MLDSA issue. Constant-last changes its global delta count by only 20 (174923 to 174903). The pure swap-to-last variant moves only two MLDSA wire IDs in total, so that placement was already almost entirely present. The same change helps both mdoc circuits modestly.
3. Fixed original inputs are a significant constraint on the largest layer. MLDSA's first layer alone has a separately compressed segmented body of 403515 bytes at zstd-16. Whole-component fan-in numbering gets that only to 400657 bytes, although it substantially improves later layers. This is a diagnostic, not an information-theoretic lower bound or an additive estimate for whole-file compression.
4. Later layers also matter. At depths 34/35/36, separately compressed baseline bodies are 107692/164188/106523 bytes; whole-component fan-in numbering changes these to 55727/78937/54667. Thus the observed gain is not primarily in the immutable-input layer.
5. These experiments neither modify nor test a different FFT, SHAKE basis, comparator implementation, unroll period, or arithmetic circuit. They cannot establish a quadratic FFT bug. They isolate wire-label/order effects on the existing circuit. They also do not prove 500 kB impossible under legal renaming.

A sensible next scheduling investigation is a **joint producer/consumer structural ordering** which preserves existing repeated difference patterns across adjacent layers, with fixed input anchors. Independently minimizing component span or sorting full fan-in lists is insufficient. This is a direction to investigate, not a claimed working policy. There is no application-name branch, component-size majority threshold, or try-several-and-pick policy added here.

## Decoder and proof validation

Every high-compression candidate was read by the existing LFC2 decoder with circuit-ID verification and compared exactly against its canonical LFC1 stream. No normalization step or auxiliary map is needed. Wire renaming changes the circuit ID, so proofs must bind to the renamed circuit; the existing circuit's proof is not reused.

Single-run LFC2 decoding with ID computation (without outer zstd decompression), milliseconds:

| Policy | Signature | Hash | MLDSA44 |
|---|---:|---:|---:|
| Baseline | 9.891 | 122.549 | 210.484 |
| Constant-last | 9.728 | 122.036 | 209.478 |
| Whole-component fan-in | 9.707 | 165.239 | 203.362 |

These are diagnostic timings under concurrent experiment load, not isolated performance benchmarks.

A complete MLDSA44 proof was generated and verified from the stock-decoded segmented circuit using the unchanged original input vector:

| Measurement | Baseline | Constant-last |
|---|---:|---:|
| Circuit inputs | 128272 | 128272 |
| Witness count reported by runtime | 125766 | 125766 |
| Constraints | 37 | 37 |
| Encoded block size | 5699 | 5699 |
| Proof bytes, deterministic benchmark | 665736 | 665096 |
| Commit time, seconds | 0.897 | 0.891 |
| Prove time, seconds | 2.545 | 2.517 |
| Verify time, seconds | 2.187 | 2.176 |

The 640-byte proof difference is consistent with transcript-dependent opening lengths after changing the circuit ID, not a change in proof geometry; it is not a guaranteed saving for other transcripts. Both proofs passed. Mdoc candidates received exact inverse and decoder validation; a full mdoc proof was not run for the experimental layouts. The default mdoc production path is unchanged.

Five unit tests passed in each fixture's included experiment module (15 test executions), including explicit rejection of private-input renumbering, dense constant placement, pure two-wire swapping, and tiny-circuit geometry/input/Morton checks.

## Reproduction

Screen only legal wire layouts, compiling each fixture once per batch:

```sh
MORTON_ORDER_SWEEP=1 SWEEP_WIRE_ONLY=1 \
SWEEP_WIRE_BATCH=identity,identity_one_last,whole_fanin \
cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
```

Use the same environment with `-p mdoc-zk-circuits analyze_signature_morton` and `analyze_hash_morton`. Add `SWEEP_FINAL=1 SWEEP_LAYER_STATS=1` for all three formats, high-compression checks, decoding and per-layer body measurements. The complete policy list and results are in WIRE_ONLY_DATA.md; the bit families use rotate2..12, bitrev3..12, xor1..12.

```sh
MLDSA_WIRE_POLICY=identity_one_last \
cargo test -p circuits-experimental mldsa44_proof_benchmark -- --ignored --nocapture

cargo test -p circuits-experimental order_sweep::layer_wires::tests -- --nocapture
```

Screening records, final-format/per-layer records and both proof logs are under [results/](results/), named `wire-screen*`, `wire-final-*`, `wire-final2-*`, `wire-proof-*` and `wire-unit-*.log`. Four initial swap-placement records were replaced by the corrected pure-swap implementation's results in screening batch 3; the superseded records are excluded from the archived batch 2 and all tables.
