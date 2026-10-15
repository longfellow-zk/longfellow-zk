# Morton traversal / component-template experiment

Fixed period 6; results from the current workspace, 2026-09-11.

Follow-up: [differencing Morton keys while keeping the original traversal](MORTON_KEY_REPORT.md).

Follow-up: [lexicographic traversal with unchanged LFC2 segmentation](LEX_ORDER_REPORT.md).

Follow-up: [per-layer bipartite component layout](BIPARTITE_REPORT.md).

## Conclusion

Absolute Morton translation sensitivity **does destroy repetition in corresponding SHAKE components** in this MLDSA-44 circuit. This is demonstrated on matching internal wiring, not inferred from equal component sizes. It is not the entire compression problem: storing local components with independently encoded absolute maps also loses important repetition between instances.

A single experimental encoding rule, `LCT1`, addresses both problems. It reaches **473,218 bytes at zstd-22** for MLDSA-44, versus 1,606,804 for canonical LFC1. The same rule improves both mdoc circuits. At zstd-16 MLDSA is **500,470 bytes**, just above a strict 500,000-byte target (below 500 KiB). No extra witnesses, changed wires, or increased proof size are needed.

This is a storage-format prototype, **not a production scheduler change**. The scheduler, including its pre-existing component-size majority switch, was frozen throughout this investigation. These results do not justify that switch as a universal scheduling policy. The prototype has neither a component-size threshold nor application-specific branches, and does not compress two alternatives and select a winner.

## Explicit correspondence and causal controls

Components are recovered from the already compiled, layered circuit. Original inputs are boundary ports. Constant-only wires, including wire 0 and its copies, are also boundary ports, not connectivity edges. There are 37 known constant wires including input wire 0 in the MLDSA fixture. Shared-wire references remain in the encoded maps.

One explicitly verified pair is component **212441 / 327440** (IDs are flattened compiled-wire indices). Their assertion paths include:

```
mldsa_verify/sample_in_ball/shake256/keccak_f_1600_xor/
  keccak_f_1600_xor.11/assert_eq_xor_state/.../xor_lane
mldsa_verify/shake256/keccak_f_1600_xor/
  keccak_f_1600_xor.11/assert_eq_xor_state/.../xor_lane
```

Each has 85,901 wires and 117,828 terms across 37 layers, including compiler copy chains. Verification compares every local gate/operand/coefficient, boundary-port type and constant value, and every internal input's mapping to the previous layer's local output. Exact vectors are compared; hash equality alone is not accepted. The port map explicitly permits different absolute input wires. This establishes full layered-DAG correspondence, not just independent layer similarities.

There are three such families of eight components (slices ending at rounds 11, 17, 23), plus one family of five 87,501-wire / 120,516-term components (round 5). The three remaining SHAKE-sized components are not asserted to be identical to these families. The 1,000-wire cutoff in the *diagnostic listing* just suppresses tiny components; the encoding includes every component and has no such cutoff.

For the first pair:

- Existing ascending wire ranks already establish exact correspondence. Structural relabeling is not needed.
- Outputs and internal inputs differ by uniform translations in **36/37 layers**. The first layer is entirely boundary inputs.
- After excluding all terms touching shared inputs/constants, absolute Morton traversal still differs in **35/36 internal layers**: 56,820 sequence positions differ.
- Including shared-port terms, only 1/37 normalized layer sequences matches; 57,406 positions differ.
- Both the rank-based and structural correspondence searches find the same four large SHAKE families. Structural relabeling changes compression statistics, but uncovers no additional large families in this fixture. This is not a general graph-isomorphism completeness claim.

A concrete inversion in layer 2 (layers counted from the inputs):

| Term | First component `(g,h0,h1)` | Corresponding second component |
|---|---|---|
| A | `(81265,84682,84874)` | `(180292,199681,199873)` |
| B | `(81393,84618,85450)` | `(180420,199617,200449)` |

Both terms have coefficient index 0. The translations are `g += 99027`, `h0,h1 += 114999`. Neither term touches a boundary port. Absolute Morton puts A before B on the left and B before A on the right. Subtracting those bases gives identical wiring. Thus neither different internal permutations nor shared constants can explain this inversion.

## Traversal, deltas, and repetition

Two local coordinate systems are measured separately:

1. **Offset**: subtract the component's output base and preceding-layer component base, preserving gaps between internal wire numbers; name shared wires as explicit local ports.
2. **Rank**: additionally pack the component's used wires into ascending dense local ranks. This is used by the template encoder; the full inverse maps are stored.

Within each comparison, coordinates and component boundaries are identical. Only the traversal changes from the normalized subsequence of the original absolute Morton stream to local Morton. Deltas are ordinary coordinate subtraction. `k` is a coefficient-table index, not a subtracted coordinate.

Distinct delta records `(Δg,Δh0,Δh1,k)`:

| Traversal / coordinates | mdoc signature | mdoc hash | MLDSA-44 |
|---|---:|---:|---:|
| Original global absolute Morton | 14,192 | 18,449 | 174,923 |
| Component subsequences, offset coordinates | 12,437 | 17,508 | 134,364 |
| Local Morton, offset coordinates | 12,598 | 17,747 | **68,527** |
| Component subsequences, rank coordinates | 12,017 | 13,996 | 134,362 |
| Local Morton, rank coordinates | 12,040 | 13,669 | 68,619 |
| Structural relabeling + local Morton | 13,423 | 44,937 | 54,744 |

Counting only coordinate triples, the MLDSA offset comparison is **120,225 → 57,357**. On interior-only terms, the offset comparison is **130,032 → 59,590** delta records, or **117,306 → 49,906** coordinate triples. This control removes shared-wire interference and dense-rank packing as explanations for the main traversal improvement.

Exact 32-delta sequence repetition in offset coordinates:

| Circuit | Full chunks | Unique chunks: absolute subsequence → local | Occurrences belonging to repeated chunks: absolute → local |
|---|---:|---:|---:|
| mdoc signature | 7,829 | 4,255 → 4,229 | 3,989 → 4,111 |
| mdoc hash | 130,650 | 10,258 → 10,217 | 124,290 → 124,852 |
| MLDSA-44 | 185,027 | **65,749 → 19,434** | **127,933 → 175,450** |

Chunks restart at each component/layer boundary; incomplete tails are excluded from this statistic only. Every term, including tails, is encoded. Original global chunks have different boundaries, so their counts are not directly comparable to this table. Whole template equality is exact and does not depend on 32-term alignment.

Notice that local Morton slightly *increases* offset delta counts on mdoc. Minimizing distinct deltas alone is not a sufficient storage objective. The measured traversal problem is much stronger in MLDSA than in mdoc.

## Why the initial component format failed, and the fixed encoding rule

`LCT0` stores each exact local component/layer template once, then visits instances by layer/component. Each instance independently stores its output and input maps as consecutive runs. It includes all shared ports and is invertible, but loses regularity **between** neighboring instances.

In the current MLDSA schedule, every component's outputs are contiguous at every layer: 279,930 output-map runs for 279,930 component/layer blocks. In mdoc hash there are 1,173,015 runs for 569,946 blocks; 111 components are fragmented, and they account for 4,183,286 of 5,038,540 terms. A component's local ranks therefore do not generally equal its absolute offsets in mdoc. Flattening these maps independently is costly even though the mappings themselves repeat regularly between corresponding instances.

`LCT1` uses this fixed rule on all three circuits:

1. Keep the existing ascending internal wire ranks. Name constants/input wires as explicit ports.
2. Sort each component/layer's terms in local Morton order and intern exact local templates. No equal-size assumption is used.
3. Group instances by exact template; order them by layer and output-wire map.
4. Encode the first output/input map as runs of consecutive absolute wires. For subsequent instances, encode coordinate-wise differences from the preceding instance's map, run-length encoding equal differences.
5. Store all geometry, coefficients, the original circuit ID, template records, instance counts/layers, and every map. Decode, expand, and restore canonical absolute Morton order before ID verification or runtime use.

For translations, step 4 represents a whole internal map as one constant-difference run; shared constants give zero-difference runs. Sparse but correspondingly translated layouts work too. Arbitrary mappings remain representable as shorter runs or singleton differences. The initial map uses consecutive runs because differencing it against an all-zero vector would destroy its ramp structure. This is a fixed predictor with a first-record initialization, not selection between compressed alternatives.

The encoding rule preserves both *within-template* repetition and *between-instance* mapping regularity. That is the causal reason to prefer it over merely visiting whole components in order. Local traversal alone, with absolute coordinates fed to LFC1, reduces MLDSA zstd-22 only to 1,341,913 bytes and regresses mdoc hash to 509,114 bytes.

## Complete encoded sizes

All sizes below are **bytes**, not KiB. Compression is `zstd::bulk::compress` with no external dictionary. `LFC2 native` serializes the compiler result directly; `LFC2 segmented` first calls `segment_circuit`, as the existing MLDSA benchmark does. Both preserve the same canonical terms and ID. These variants are reported separately to avoid comparing different segmentation policies without labeling them.

| Circuit | Representation | Raw | zstd-16 | zstd-22 |
|---|---|---:|---:|---:|
| mdoc signature | LFC1 | 3,134,392 | 93,955 | 89,077 |
| | LFC2 native | 504,284 | 111,631 | 104,942 |
| | LFC2 segmented | 273,192 | 125,279 | 117,854 |
| | **LCT1 grouped templates** | **911,882** | **76,174** | **72,606** |
| mdoc hash | LFC1 | 60,467,613 | 133,225 | 117,606 |
| | LFC2 native | 8,282,212 | 145,896 | 132,035 |
| | LFC2 segmented | 598,054 | 173,602 | 161,848 |
| | **LCT1 grouped templates** | **23,732,738** | **95,874** | **84,284** |
| MLDSA-44, period 6 | LFC1 | 78,996,522 | 1,768,703 | 1,606,804 |
| | LFC2 native | 15,360,525 | 2,020,305 | 1,872,965 |
| | LFC2 segmented | 4,830,797 | 2,197,840 | 2,091,823 |
| | **LCT1 grouped templates** | **8,457,602** | **500,470** | **473,218** |

LCT1 raw-byte accounting (sums equal the complete raw sizes above):

| Circuit | Header incl. coefficients / ID | Template records | All wire maps | Instance/group metadata |
|---|---:|---:|---:|---:|
| mdoc signature | 19,658 | 851,310 | 35,363 | 5,551 |
| mdoc hash | 5,009 | 18,004,367 | 5,153,312 | 570,050 |
| MLDSA-44 | 26,884 | 6,691,055 | 1,458,873 | 280,790 |

The maps include **11,068 / 891,631 / 3,464,888 shared-port entries**, respectively. There are **48 / 99 / 828 templates** and **5,500 / 569,946 / 279,930 instances**. These are per-component/layer templates, not a claim that the entire circuit is made from 828 identical whole components. No encoder graph, debug symbols, external template dictionary, or input map is needed by the decoder. The field implementation is supplied by the caller, as with the existing reader APIs; the prototype has not standardized field-ID dispatch.

For completeness, unsuccessful/control encodings:

| Circuit | Encoding | Raw | zstd-16 | zstd-22 |
|---|---|---:|---:|---:|
| mdoc signature | LCT0 rank maps | 941,903 | 92,701 | 87,031 |
| mdoc hash | LCT0 rank maps | 27,847,580 | 1,544,311 | 1,158,694 |
| MLDSA-44 | LCT0 rank maps | 10,581,224 | 1,200,861 | 1,045,638 |
| mdoc signature | LCT0 structural relabeling | 1,707,273 | 189,324 | 179,086 |
| mdoc hash | LCT0 structural relabeling | 33,368,598 | 1,604,125 | 1,500,170 |
| MLDSA-44 | LCT0 structural relabeling | 21,418,820 | 1,216,144 | 1,019,876 |
| mdoc signature | Local traversal, absolute-coordinate LFC1 | 3,134,392 | 97,066 | 89,442 |
| mdoc hash | Local traversal, absolute-coordinate LFC1 | 60,467,613 | 962,605 | 509,114 |
| MLDSA-44 | Local traversal, absolute-coordinate LFC1 | 78,996,522 | 1,521,286 | 1,341,913 |
| mdoc signature | Local traversal, segmented LFC2 | 299,757 | 142,764 | 126,504 |
| mdoc hash | Local traversal, segmented LFC2 | 5,688,930 | 2,243,881 | 1,527,863 |
| MLDSA-44 | Local traversal, segmented LFC2 | 6,607,337 | 2,455,320 | 2,037,590 |

The last six rows are storage-only controls: their serialized traversal has a different ID and **must not** be fed directly to the existing sumcheck runtime. LCT0/LCT1, in contrast, restore canonical order during decoding.

## Decoder, circuit IDs, and proofs

`core/proto/src/layer.rs::compare_term` orders by absolute Morton `(h0,h1)`, then `g`, then actual serialized field coefficient. `core/proto/src/circuit.rs::compute_id` hashes the ordered absolute terms, not a traversal-independent multiset. `runtime/sumcheck/src/hquad.rs` combines adjacent equal corners and adjacent even/odd corners while folding. Consequently local traversal cannot simply replace runtime traversal.

The prototype decoder expands all maps, restores operand symmetry (`h0 <= h1`), sorts by the actual canonical comparator including coefficient bytes, reconstructs ordinary coordinate deltas, and checks the original ID. **All three decoded circuits reserialize to byte-identical canonical LFC1.** This checks every wire/term, coefficient table, geometry field, ordering choice, and ID—not just equal totals. Representation-specific LFC2 segment dictionaries need not be byte-identical.

Median of three warm decoding runs, optimized test build, one benchmark at a time. All columns include zstd-16 decompression, decoding, and ID computation; encoding/compression and subsequent equality checks are excluded:

| Circuit | LFC1 | LFC2 native | LCT1 | LCT1 sort alone, approximately |
|---|---:|---:|---:|---:|
| mdoc signature | 10.78 ms | 10.59 ms | 28.54 ms | 11.8 ms |
| mdoc hash | 152.75 ms | 151.58 ms | 580.89 ms | 296.8 ms |
| MLDSA-44 | 234.43 ms | 237.29 ms | 773.17 ms | 394.4 ms |

This decoder prioritizes checking the hypothesis, not load speed: comparison sorting is `O(T log T)`, with `O(T)` temporary storage. The MLDSA absolute-term array alone is about 105 MB; peak memory was not measured. Radix sorting, streaming layer reconstruction, and map-expansion optimization remain possible. Timings do not include optional subsequent segment recompression. No production decoder performance claim is made.

Fixed geometry:

| Circuit | Inputs | Public inputs | Outputs | Wires | Terms | Layers | Assertions |
|---|---:|---:|---:|---:|---:|---:|---:|
| mdoc signature | 4,773 | 1 | 6 | 167,739 | 259,551 | 19 | 4,796 |
| mdoc hash | 284,717 | 1 | 16 | 2,635,391 | 5,038,540 | 20 | 303,413 |
| MLDSA-44 | 128,272 | 5,121 | 2,263 | 3,449,557 | 6,580,787 | 37 | 144,961 |

MLDSA full proof generation and verification pass both before and after template roundtrip. Both proofs are **665,736 bytes**, with **125,766 commitment witnesses**, **37 constraints**, and **block_enc = 5699**. The decoded circuit goes through the existing segmentation/runtime reader/prover/verifier path. Witness generation, period, field, proof configuration, and transcript setup are unchanged. The two proof byte streams were not separately compared, but canonical circuit bytes were compared exactly. No mdoc proof rerun was performed: both committed-ID regression tests and exact circuit roundtrips pass, so the storage transformation supplies the identical circuit to any unchanged proof workflow.

## Recommendation and limits

Separate the *storage traversal* from the *runtime traversal*. Retain stable existing wire ranks, reuse exact component-local templates, and encode instance maps relative to corresponding maps. Restore canonical absolute Morton order at the storage boundary. This is a concrete single representation with a causal explanation and positive results on all three requested fixtures; it is not evidence that every circuit should use component-major wire numbering.

There is no need to change the in-circuit FFT, unroll period, XOR basis, witness count, or scheduler to reach the measured zstd-22 size. Those may have separate optimization opportunities; this experiment does not attribute all circuit complexity or the entire C++/Rust gap to Morton order.

`morton.rs` is deliberately an offline trusted-input prototype. Before production integration it needs a reviewed format specification/field dispatch, bounded decoding and malformed-input tests, memory/load-time work, and broader fixture coverage. MLDSA-65 was not measured here. The existing majority-threshold scheduler is not endorsed or replaced by this experiment.

## Reproduction

From the Rust workspace, with the current scheduler/source and SHAKE period 6:

```sh
cargo test -p mdoc-zk-circuits analyze_signature_morton -- --ignored --nocapture
cargo test -p mdoc-zk-circuits analyze_hash_morton -- --ignored --nocapture
cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture

# Faster causal controls, no compression sweep:
MORTON_DIAGNOSTICS_ONLY=1 cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
MORTON_DIAGNOSTICS_ONLY=1 cargo test -p mdoc-zk-circuits analyze_ -- --ignored --nocapture --test-threads=1

# Three-repeat, decompression-inclusive load measurements:
MORTON_DECODE_ONLY=1 cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
MORTON_DECODE_ONLY=1 cargo test -p mdoc-zk-circuits analyze_ -- --ignored --nocapture --test-threads=1

cargo test -p compile-compiler
cargo test -p mdoc-zk-circuits morton_analysis::tests
cargo test -p mdoc-zk-circuits test_serialize_and_verify_mdoc -- --nocapture
cargo test -p circuits-experimental mldsa44_proof_benchmark -- --ignored --nocapture
MLDSA_TEMPLATE_ROUNDTRIP=1 cargo test -p circuits-experimental mldsa44_proof_benchmark -- --ignored --nocapture
```

The three small diagnostic tests cover an explicit Morton translation inversion, map roundtripping including permutations/shared ports, and exclusion of shared inputs/copies of one from connectivity. Compiler tests: 28 passed. Both mdoc ID tests passed. Full size/roundtrip runs and both proof runs passed. Raw measurement logs are in [results/](results/).
