# Layer-local templates: size, native runtime, and bipartite components

Historical experiment: **LTP1 was abandoned at the user's request.** Its runtime
support and decoder have been removed. The offline discovery code is now used
to order ordinary LFC2 circuits. Commands and performance below describe the
earlier experiment, not the current worktree.

Measured 2026-09-12 on the current dirty `rust` worktree (base HEAD
`fa578cc5bb055d72df379dc195393ea2f124788e`), Ryzen 9950X, Rust 1.97.1,
release/native builds. These are comparisons against the **current saved LFC2
circuits**, not a clean-HEAD or C++ performance comparison.

## Outcome

Implemented experimental **LTP1**, a layer-addressable template format consumed
directly by the dense hand-major prover, numerical verifier, and symbolic
verifier through the shared layer iterator. No expansion to all absolute terms,
runtime sort, runtime hash table, or sparse binding is required.

A single global-component / shape-first template policy gives:

- MLDSA-44: **507,336 bytes** with zstd-22, versus LFC2 959,815.
- MLDSA-65: **509,971 bytes**, versus 989,616.
- Current two-attribute mdoc combined archive: **98,898 bytes**, versus 162,101.

This **does not meet a strict 500,000-byte target**. It also does not dominate
LFC2: the best-zstd representation is substantially larger uncompressed and slows
mdoc proving. Defaults remain LFC2. There is no runtime “try both and choose”
policy and no component-size majority threshold.

Layer bipartite components do have value, but there is a measurable cost to
fragmentation. Excluding one/copies gives much smaller local programs and far more
instance mappings. Including one improves the mdoc hash result, but is worse than
the global policy on MLDSA. Details below separate those effects.

## Format and traversal

The circuit header contains the LTP1 magic, field fingerprint, geometry,
coefficient table, and the existing traversal-dependent circuit ID. Every layer
has its input width/log-width and a byte length. Layers are in prover order,
output to input, and can be decoded independently after the circuit header.

A layer contains groups. Each group stores:

1. One exact local program of `(g, h0, h1, coefficient-index)` records.
2. Its local output-map length and combined output/input-map length.
3. An instance count and a packed stream of instance maps.

For a mapped instance, local output indices select entries in the output map;
local input indices select entries in its input map. Shared inputs and constants
are explicit ports: **all their mapping bytes are counted**. The global builder
canonicalizes mapped operands back to the original absolute min/max hands.
This preserves every original term, including duplicates; it is not merely an
isomorphism or equal-wire-count check.

The first map uses consecutive absolute runs. Subsequent maps use signed
coordinate differences, runs of equal differences, and repetition of entire
difference vectors. The runtime needs only the current map and, for repeated
instances, one difference map. A single-instance group does not allocate the
second map. There is no requirement for contiguous global `g` or Morton order
in the hand-major consumer.

Experimental local program codecs:

| Codec | Local program |
|---|---|
| 0 | Row-wise signed coordinate deltas; absolute coefficient IDs |
| 1 | Same values in four columns |
| 2 | Bitpacked absolute-coordinate columns |
| 3 | Literal/repeat packets over the columns |
| 4 | Column deltas, including coefficient-index deltas |
| 5 | Literal/repeat packets, including coefficient-index deltas |
| 6 | Local delta dictionary, fixed 16-term segment dictionary, segment tokens; coefficient deltas |
| 7 | Same segmentation, but absolute coefficient IDs as in LFC2 |

Codecs 0–5 remain packed byte programs in memory; codecs 6–7 load native
dictionaries and references, not expanded terms. The offline writer can use hash
tables; the decoder and prover do not. Each file specifies its codec explicitly.

The common layout policy uses global components with original inputs and proven
constants excluded from connectivity, projects each component into each layer,
normalizes its local wiring, and groups **exactly matching** local programs.
Within a program: constant/linear/square/product shape, descending local output,
descending second input, ascending first input, then coefficient bytes.
This follows the current compiler's shape-first ordering, applied locally.
The same policy and codec are used for every circuit in the main comparison.

Codec 4 is the compression-oriented candidate. Codec 5 trades some zstd size for
smaller raw storage. Codecs 6–7 demonstrate native segmentation, but their
dictionary-reference streams compress worse. These are explicit research
profiles, not a proposed per-circuit automatic selector.

## Serialized sizes

All numbers are bytes. Standalone circuits use zstd bulk compression; all headers,
coefficients, mappings, and shared-wire overhead are included.

| Circuit | LFC2 raw | LFC2 zstd-22 | LTP1-4 raw | LTP1-4 zstd-16 | LTP1-4 zstd-22 | LTP1-5 raw | LTP1-5 zstd-22 |
|---|---:|---:|---:|---:|---:|---:|---:|
| MLDSA-44 | 2,670,639 | 959,815 | 7,040,840 | 516,146 | 507,336 | 3,171,956 | 526,993 |
| MLDSA-65 | 2,896,804 | 989,616 | 7,906,285 | 520,652 | 509,971 | 3,455,499 | 529,905 |
| mdoc hash 1 | 528,666 | 99,426 | 24,801,062 | 64,104 | 61,862 | 14,957,795 | 79,066 |
| mdoc hash 2 | 548,467 | 100,969 | 26,327,430 | 66,537 | 63,811 | 15,866,790 | 81,570 |
| mdoc hash 3 | 564,388 | 101,976 | 27,853,543 | 67,816 | 64,912 | 16,775,496 | 82,471 |
| mdoc hash 4 | 581,388 | 102,791 | 29,379,530 | 68,879 | 65,747 | 17,684,077 | 82,920 |
| mdoc signature | 222,143 | 63,398 | 954,302 | 38,947 | 37,194 | 503,080 | 40,057 |

The actual two-attribute LFA2 archive uses the production streaming compressor
and includes its archive overhead. It is not the sum of independently compressed
entries:

| Archive representation | Raw | zstd-16 | zstd-22 |
|---|---:|---:|---:|
| LFC2 | 770,782 | 183,465 | 162,101 |
| LTP1-4 | 27,281,905 | 103,332 | 98,898 |
| LTP1-5 | 16,370,043 | 126,417 | 118,942 |
| LTP1-6 | 1,494,151 | 195,397 | 177,484 |
| LTP1-7 | 1,522,195 | 205,404 | 184,709 |

For comparison, on the **same current fixtures**, the preceding LCT1 format was
8,156,804 raw / 729,506 zstd-22 bytes for MLDSA-44 and
9,277,493 / 764,666 for MLDSA-65. An older reported 473,218-byte MLDSA-44 LCT1
result belongs to a different saved layout/fixture; it was not reproduced here.
Current MLDSA LFC1 controls are 78,996,522 / 616,173 and 95,475,126 / 640,820
raw / zstd-22 respectively.

### Segmentation and delta counts

Counts below sum **per-template dictionary sizes**, not the cardinality of one
global absolute-delta set. Codec 4 has no delta dictionary.

| Circuit | Codec | Raw bytes | zstd-22 | Local deltas | Local segments |
|---|---:|---:|---:|---:|---:|
| MLDSA-44 | 6 | 3,315,745 | 798,572 | 277,920 | 47,914 |
| MLDSA-44 | 7 | 3,846,852 | 770,387 | 363,327 | 49,869 |
| MLDSA-65 | 6 | 3,462,485 | 799,570 | 278,512 | 48,335 |
| MLDSA-65 | 7 | 3,993,290 | 792,288 | 364,220 | 50,290 |
| mdoc hash 2 | 6 | 1,265,850 | 111,950 | 16,890 | 10,886 |
| mdoc hash 2 | 7 | 1,283,774 | 116,709 | 17,967 | 10,893 |
| mdoc signature | 6 | 228,129 | 67,596 | 10,283 | 6,705 |
| mdoc signature | 7 | 238,249 | 69,794 | 11,794 | 6,795 |

Using absolute coefficients did **not** reduce dictionary cardinality here.
Frequency-ordering dictionary IDs reduced raw size but worsened zstd relative to
the first-use control: MLDSA-44 codec 6 changed from 3,404,946 / 759,014 to
3,315,745 / 798,572. Therefore “fewer/smaller indices” is not by itself a reliable
prediction of compressed size.

## Bipartite components: what changes and why

Each layer has distinct input/output vertex sets. An edge represents a term's
input dependency. Components are ordered by minimum wire ID across both sets,
with a deterministic tie break. Original circuit inputs remain ports in both
variants. The exclusion variant also removes proven one wires and their copies
on both sides. An inclusion control deliberately allows those wires to connect
components, as requested for the experiment.

| Circuit | Exclude one: nonempty components summed over layers | Largest terms | Include one: components | Largest terms |
|---|---:|---:|---:|---:|
| MLDSA-44 | 1,640,739 | 10,240 | 658,699 | 234,117 |
| MLDSA-65 | 1,759,366 | 12,800 | 746,111 | 240,514 |
| mdoc hash 2 | 1,765,254 | 143,364 | 1,339,955 | 2,566,435 |
| mdoc signature | 107,099 | 13,608 | 53,930 | 41,113 |

With identical explicit-map encoding, whole-component grouping, shape-first
local ordering, and codec 4:

| Circuit | Global zstd-22 | Bipartite exclude one | Bipartite include one |
|---|---:|---:|---:|
| MLDSA-44 | 507,336 | 905,118 | 705,312 |
| MLDSA-65 | 509,971 | 851,963 | 691,531 |
| mdoc hash 2 | 63,811 | 126,595 | **58,890** |
| mdoc signature | **37,194** | 83,283 | 37,755 |

The global control excludes **all proven constants**, while this local
experiment varies one/copies specifically. This comparison does not isolate
graph scope from the constant-boundary rule. It does establish that the tested
bipartite policy is not an across-the-board replacement.

The causal tradeoff is visible before zstd:

| Circuit / split | Stored local terms | Instances | Program bytes (codec 4) | Mapping bytes |
|---|---:|---:|---:|---:|
| MLDSA-44 global | 1,467,694 | 279,930 | 6,267,662 | 739,154 |
| MLDSA-44 bipartite exclude one | 513,417 | 1,640,739 | 2,181,802 | 10,324,340 |
| MLDSA-44 bipartite include one | 3,847,497 | 658,699 | 16,806,176 | 4,309,058 |
| mdoc hash 2 global | 6,328,859 | 39,005 | 25,869,759 | 451,885 |
| mdoc hash 2 bipartite exclude one | 576,503 | 1,765,254 | 2,581,247 | 5,815,181 |
| mdoc hash 2 bipartite include one | 4,707,309 | 1,339,955 | 19,315,619 | 5,016,099 |

Thus, smaller components really do recover more exact local-program reuse.
However, the MLDSA exclusion policy saves about 4.1 MB of program while adding
9.6 MB of mappings. The graph split does not make these shared ports disappear.
Conversely, the large mdoc program is highly regular and zstd compresses it very
well despite its poor raw size. Connectivity is not a sufficient cost model.

Additional controls included gate-aligned windows, affine versus explicit maps,
row versus column map differences, local Morton order, lexicographic directions,
coefficient-table reorderings, packets, bitpacking, and segmentation. A mapped
bipartite inclusion control with codec 0 reaches **57,585 bytes** for mdoc hash 2.
This is evidence of useful local structure, not a reason to choose a different
policy automatically per circuit. Changing coordinate directions saved only
9–10 bytes on MLDSA; the common shape-first policy was retained.

Independent layer compression identifies the input-adjacent MLDSA layer
(prover depth 36) as the largest contributor: 88,245 / 89,325 bytes for
MLDSA-44/65 under codec 4. Depths 2 and 1 follow. The bipartite policies increase
depth 36 to 159,009 / 139,339 bytes. These per-layer sizes cannot be summed to
predict whole-file zstd size because cross-layer repetition matters.
This experiment does not attribute the remaining bytes to FFT versus SHAKE;
it changes representation, not arithmetic or gate generation.

## Prover/verifier performance and actual memory

Five sequential timing repetitions per profile, medians below. No concurrent
builds or proof benchmarks during timing. Timing runs use the normal allocator.
Memory runs use a separate tracked-allocator binary and one proof in each fresh
process. RSS comes from `/usr/bin/time -v`; heap values are measured live Rust
allocation high-water marks, not capacity estimates.

For MLDSA, prover = commit + prove; circuit file loading, ID checking, witness
setup, and proof serialization/deserialization are outside the crypto timer.
For mdoc, these are full current application prover/verifier calls, including
archive decompression/decoding, setup, and proof serialization. Correction from
the subsequent speed investigation: the application loader passes
`enforce_circuit_id=false`; it does not recompute circuit IDs in this timer.
Archives are prepared in another process so zstd compression cannot contaminate
the reported peak RSS. Runtime mdoc uses the zstd-16 archives above.

| Circuit | Profile | Prover ms | Verifier ms | Process peak RSS MiB | Prover / verifier live-heap peaks MiB |
|---|---|---:|---:|---:|---:|
| mldsa44 | LFC2 | 1133.6 | 677.6 | 121.7 | 118.0 / 33.4 |
| mldsa44 | LTP1-4 | 1286.3 | 680.0 | 120.7 | 117.2 / 32.9 |
| mldsa44 | LTP1-5 | 1333.7 | 694.2 | 116.9 | 113.5 / 29.2 |
| mldsa44 | LTP1-6 | 1219.5 | 650.5 | 124.2 | 119.8 / 35.6 |
| mldsa44 | LTP1-7 | 1223.3 | 640.8 | 125.2 | 121.3 / 37.0 |
| mldsa65 | LFC2 | 1261.4 | 751.4 | 131.8 | 129.5 / 40.1 |
| mldsa65 | LTP1-4 | 1452.1 | 766.5 | 131.0 | 128.9 / 40.0 |
| mldsa65 | LTP1-5 | 1528.3 | 783.9 | 125.9 | 124.7 / 35.7 |
| mldsa65 | LTP1-6 | 1371.4 | 734.1 | 133.0 | 131.0 / 42.0 |
| mldsa65 | LTP1-7 | 1360.4 | 715.2 | 135.0 | 132.5 / 43.5 |
| mdoc | LFC2 | 383.2 | 193.9 | 102.9 | 92.5 / 38.1 |
| mdoc | LTP1-4 | 654.3 | 317.9 | 128.6 | 121.1 / 66.7 |
| mdoc | LTP1-5 | 699.0 | 332.2 | 118.7 | 110.7 / 56.3 |
| mdoc | LTP1-6 | 426.4 | 228.2 | 106.0 | 99.1 / 44.7 |
| mdoc | LTP1-7 | 437.0 | 227.4 | 106.5 | 99.2 / 44.8 |

The MLDSA verifier heap includes the circuit and the prepared input vector held
by this combined benchmark; it is not a minimal standalone verifier process.
RSS is a **whole-process** peak, not a per-phase verifier RSS. The CSV provides
both total and additional live-heap peaks for each phase. Tracked-run times are
not used as performance results.

Codec 4 MLDSA load+ID median costs are 256.4 / 309.4 ms, versus LFC2
191.3 / 231.3 ms. Decoder-only single-run observations, excluding ID hashing,
were approximately 23 / 27 ms for codec 4 and 14 / 16 ms for codec 6.
Do not confuse those different measurements.

The mdoc slowdown is consistent with repeatedly reading a 26 MB packed local
program versus the small existing segmented representation, plus map
interpretation and more expensive decoding. Codec 6 brings mdoc
proving down to 426 ms, but its archive is **larger than LFC2 after zstd**.
Direct consumption is implemented; it is not free decoding.

## Circuit and proof invariants

SHAKE period 6, XOR basis, arithmetic, CRT interpolation, witness count, widths,
depth, and term multiset are unchanged. Inputs are not renamed. No gates,
constraints, witnesses, or copy wires are inserted or removed.

| Circuit | Layers | Terms | Wires including original inputs | Inputs |
|---|---:|---:|---:|---:|
| MLDSA-44 | 37 | 6,580,787 | 3,577,829 | 128,272 |
| MLDSA-65 | 37 | 7,953,988 | 3,756,007 | 156,263 |
| mdoc hash 2 | 20 | 6,394,835 | 3,473,933 | 77,785 |
| mdoc signature | 21 | 276,481 | 183,618 | 3,941 |

Earlier wire reports excluded original inputs: MLDSA-44/65 were
3,449,557 / 3,599,744 on that convention. The difference is not new wires.

The circuit-ID algorithm is unchanged. Its implementation now consumes the
shared delta visitor so it can hash either representation. Existing LFC1/LFC2
fixture IDs still match. Regrouping terms changes the traversal and therefore
the ID; experimental mdoc archives use the correspondingly updated trusted ID.
No canonical-order hashing is substituted.

| Circuit | LFC2 proof bytes | Template proof bytes (all codecs 4–7) |
|---|---:|---:|
| MLDSA-44 | 665,416 | 665,800 |
| MLDSA-65 | 719,368 | 718,792 |
| mdoc two attributes | 344,236 | 343,660 |

Proof geometry and security parameters are unchanged. The small baseline versus
template byte differences arise with the changed ID/transcript and Merkle
multiproof path sharing; **exact serialized proof size is not invariant**.
All template codecs preserve the same traversal/ID. MLDSA codecs 5–7 were checked
against codec 4's proof bytes, and both MLDSA circuits were also expanded to an
ordinary delta layer with the same traversal and produced exactly the same proof.
The generic full-ZK test compares byte-identical proofs for LFC1, LFC2, and
codecs 0–7 with the same traversal.

Numerical and symbolic verifier paths use the same visitor. Legacy round-major
proving is intentionally rejected for template layers: this experiment does not
promise Morton traversal. Existing LFC1/LFC2 round-major support remains intact.

## Validation and reproduction

Passed:

- `cargo check --workspace --all-targets`
- `cargo clippy -p core-proto --lib -- -D warnings`
- `cargo test --release -p core-proto -p runtime-sumcheck -p runtime-zk`
- Full MLDSA-44/65 and current two-attribute mdoc proof roundtrips for LFC2 and
  codecs 4–7, with the saved-circuit benchmark harness.
- Full ZK symbolic/layout/tampering tests, malformed-format tests, exact
  per-layer term-multiset checks, ID checks, and codec reserialization checks.

Strict clippy for the experimental proof target encounters an existing
`byte_char_slices` lint in mdoc hash constants; unrelated code was not changed.

Saved source fixtures are
`target/traversal-circuits/{dataset}--kind_abs_lex0213_r5.lfc2`.
The existing traversal experiment produces these inputs. Build harnesses:

```sh
cargo test --release -p circuits-experimental --test layer_templates --test template_proofs --no-run
LTP_DATASET=mldsa44 LTP_COMPONENTS=3 LTP_WINDOWS=10000000 \
LTP_MODES=0 LTP_ORDERS=4 LTP_CODECS=4,5,6,7 LTP_MAP_COLUMNS=0 \
LTP_COEFFICIENTS=original LTP_REPORT_LAYERS=1 \
LTP_SAVE_DIR=target/layer-templates-v1 \
cargo test --release -p circuits-experimental --test layer_templates -- --ignored --nocapture

LTP_PROOF_CIRCUIT=target/layer-templates-v1/mldsa44-b3-w10000000-a0-o4-c4-m0-koriginal.ltp \
LTP_REPEATS=5 cargo test --release -p circuits-experimental \
--test template_proofs mldsa44_template_proof -- --ignored --nocapture
```

For bipartite controls use `LTP_COMPONENTS=1,2`. Dataset names also include
`mldsa65`, `mdoc_hash1` through `mdoc_hash4`, and `mdoc_sig`.

Prepare mdoc separately:

```sh
LTP_SIG=target/layer-templates-v1/mdoc_sig-b3-w10000000-a0-o4-c4-m0-koriginal.ltp \
LTP_HASH=target/layer-templates-v1/mdoc_hash2-b3-w10000000-a0-o4-c4-m0-koriginal.ltp \
LTP_SAVE_ARCHIVE=target/ltp-mdoc-4.archive \
cargo test --release -p circuits-experimental --test template_proofs \
mdoc_template_proof -- --ignored --nocapture
LTP_MDOC_ARCHIVE=target/ltp-mdoc-4.archive LTP_REPEATS=5 \
cargo test --release -p circuits-experimental --test template_proofs \
mdoc_template_proof -- --ignored --nocapture
```

For memory, build with `--features bench-memory --no-run`, then run the emitted
test executable directly under `/usr/bin/time -v` with `LTP_REPEATS=1`.
Do not measure Cargo/compiler RSS as prover memory.

Raw data:

- [Size sweeps](results/layer-template-sizes.csv): 245 recorded rows, including
  repeated controls across stages; not 245 distinct policies. Early affine
  shape-order rows affected by a subsequently fixed square-classification issue
  are excluded.
- [Timing repetitions](results/layer-template-timings.csv)
- [Actual memory](results/layer-template-memory.csv)
- [Layer decomposition](results/layer-template-layers.csv)

The format remains experimental, not production-audited or enabled by default.
My recommendation is to retain the layer-local program + explicit-map interface,
use codec 4 as the reproducible compressed-size target, and **not replace LFC2
yet**. The next optimization should reduce the native cost of the large regular
local programs while preserving their zstd-friendly traversal. Bipartite
fragmentation is a useful structural tool, but its mapping overhead needs to be
addressed before it can serve as the universal partition policy.
