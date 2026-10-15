# Balanced plucker / unroll grid (hand-major, full subfield inputs, 18/3-byte fields)

## Scope and measurement

168 configurations: MLDSA-44 and MLDSA-65 × periods 1–6 × maximum packed widths 0–6 × round-0 special off/on. Width 0 is the original direct XOR-basis witness. All circuits use the same whole / shape_classes / reuse LFC2 ordering; all proving and verification is hand-major. No Morton control or per-circuit choice of ordering is used.

All circuits set `subfield_boundary = ninput`. Every native input is checked to lie in fp24 before proving. This boundary stops at the original inputs: sumcheck pad witnesses appended by the prover remain extension-field witnesses. fp24 serializes as three little-endian bytes; fp24_6 serializes as six such coefficients (18 bytes). Noncanonical coefficients and lengths are rejected. The in-memory arithmetic representation is unchanged. The proof-geometry optimizer uses these same 18/3-byte sizes. These circuits, IDs and proofs are regenerated; old 24/4-byte artifacts are not reused or silently reinterpreted.

Each 64-bit lane uses ceil(64 / width) pluckers, balanced to widths differing by at most one, larger first. Widths 1…6 give 64×1; 32×2; 20×3+2×2; 16×4; 12×5+1×4; 9×6+2×5. No padding bits are introduced. Decoder range assertions are retained, and decoded Boolean bits are converted to the existing XOR basis (1−2b).

Round-0 special adds a cut after round 0 without moving regular cuts: period 6 has [0,5,11,17,23], not [0,6,12,18,23]. Period 1 already slices after round 0; both flag values were compiled and measured anyway.

Release Rust, target-cpu=native, on the existing Ryzen 9950X host. Compilation/compression ran in parallel; proof timings ran serially after that work finished, in a fixed shuffled order (seed 20260912). Times are medians of five complete verified flows; prover includes commitment plus proving, but excludes circuit load/ID validation, native input construction and proof serialization. Verifier excludes proof parsing. Peak memory is actual process high-water RSS from a separate fresh one-flow /usr/bin/time -v run, including loading, witnesses, proving and verification. It is not an allocation estimate and does not include offline compilation. MiB = 1,048,576 bytes; the circuit target is 500,000 compressed bytes.

Proof geometry is optimized independently by the existing Ligero geometry selector with rateinv=4 and nreq=128. The security parameters and runtime algorithms are unchanged. Every measured proof is serialized, parsed and verified. Circuit/proof sizes are measured byte counts, not geometry estimates. LFC2 is directly consumed by the hand-major prover.

The largest packed circuits exceed the default reader's 20-million-total-term budget. The local experiment harness explicitly sets a 40-million-total-term budget via `ORDER_TOTAL_TERM_LIMIT`; the production default and all per-layer/dimension bounds are unchanged. Using these oversized cells outside the harness requires the same explicit reader configuration for trusted circuits.

## Common-policy candidates

Under 500,000 bytes for both circuits: **13 distinct settings** (excluding duplicate period-1 flag values). The lowest combined proof size uses `(period, bits, special) = (1, 4, 0)`; the lowest combined prover time uses `(6, 0, 1)`. These are explicit tradeoff objectives, not an adaptive encoding policy.

For the 500 KB target, retain period 6 with a special round-0 cut and direct XOR witnesses when speed is the priority. For a modest speed/size tradeoff, period 4 with the same round-0 cut and no pluckers gives 367,947 / 377,432 compressed bytes, slightly smaller proofs, and about 5% more combined prover time than period 6. Four-bit packing with period 1 minimizes proof bytes under the shared cap, but takes about 74% more combined prover time than the period-6 unpacked configuration. Following this sweep, period 4 / special round 0 / no pluckers was selected as the default for both MLDSA circuits. Other configurations remain opt-in experiments.

| Circuit | Period | Max bits | Round 0 special | LFC2 bytes | zstd-22 bytes | Proof bytes | Prover ms | Verifier ms | Peak MiB |
|---|---:|---:|:---:|---:|---:|---:|---:|---:|---:|
| mldsa44 | 4 | 0 | yes | 1,642,397 | 367,947 | 218,708 | 1,148.3 | 699.9 | 126.9 |
| mldsa65 | 4 | 0 | yes | 1,805,553 | 377,432 | 227,852 | 1,297.4 | 801.8 | 136.3 |
| mldsa44 | 6 | 0 | no | 2,629,203 | 890,331 | 218,432 | 1,074.6 | 653.4 | 121.0 |
| mldsa65 | 6 | 0 | no | 2,759,215 | 899,949 | 227,560 | 1,209.3 | 729.5 | 130.1 |
| mldsa44 | 6 | 0 | yes | 1,745,884 | 434,414 | 221,500 | 1,091.7 | 658.8 | 120.0 |
| mldsa65 | 6 | 0 | yes | 1,906,467 | 439,112 | 233,524 | 1,241.6 | 756.3 | 129.4 |
| mldsa44 | 1 | 4 | no | 2,158,481 | 419,296 | 196,412 | 1,949.0 | 1,137.8 | 205.1 |
| mldsa65 | 1 | 4 | no | 2,401,242 | 451,078 | 206,820 | 2,099.4 | 1,243.3 | 214.8 |
| mldsa44 | 1 | 0 | no | 1,318,922 | 215,054 | 270,784 | 1,581.0 | 945.5 | 191.6 |
| mldsa65 | 1 | 0 | no | 1,484,850 | 225,163 | 279,072 | 1,716.0 | 1,022.3 | 233.9 |

### Every shared setting below the circuit-size cap

Each setting below is fixed for both MLDSA circuits. No runtime format selection or per-circuit heuristic switching is involved.

| Circuit | Period | Max bits | Round 0 special | LFC2 bytes | zstd-22 bytes | Proof bytes | Prover ms | Verifier ms | Peak MiB |
|---|---:|---:|:---:|---:|---:|---:|---:|---:|---:|
| mldsa44 | 1 | 0 | no | 1,318,922 | 215,054 | 270,784 | 1,581.0 | 945.5 | 191.6 |
| mldsa65 | 1 | 0 | no | 1,484,850 | 225,163 | 279,072 | 1,716.0 | 1,022.3 | 233.9 |
| mldsa44 | 1 | 1 | no | 1,762,157 | 329,588 | 272,152 | 1,793.8 | 1,055.3 | 220.1 |
| mldsa65 | 1 | 1 | no | 1,953,564 | 344,500 | 279,856 | 1,931.4 | 1,139.8 | 242.6 |
| mldsa44 | 1 | 2 | no | 1,823,184 | 367,545 | 225,408 | 1,667.2 | 1,020.8 | 197.8 |
| mldsa65 | 1 | 2 | no | 2,027,043 | 391,946 | 231,456 | 1,803.6 | 1,033.8 | 206.6 |
| mldsa44 | 1 | 4 | no | 2,158,481 | 419,296 | 196,412 | 1,949.0 | 1,137.8 | 205.1 |
| mldsa65 | 1 | 4 | no | 2,401,242 | 451,078 | 206,820 | 2,099.4 | 1,243.3 | 214.8 |
| mldsa44 | 2 | 0 | no | 1,712,906 | 383,586 | 230,040 | 1,319.4 | 848.2 | 147.7 |
| mldsa65 | 2 | 0 | no | 1,870,831 | 389,687 | 234,088 | 1,426.6 | 837.5 | 156.7 |
| mldsa44 | 2 | 0 | yes | 1,513,664 | 277,253 | 229,340 | 1,328.3 | 796.8 | 147.8 |
| mldsa65 | 2 | 0 | yes | 1,676,818 | 286,414 | 236,884 | 1,452.3 | 859.9 | 157.5 |
| mldsa44 | 2 | 1 | yes | 1,956,608 | 406,497 | 231,724 | 1,446.9 | 841.6 | 160.6 |
| mldsa65 | 2 | 1 | yes | 2,139,403 | 423,246 | 239,276 | 1,581.4 | 919.5 | 169.1 |
| mldsa44 | 2 | 2 | yes | 2,025,290 | 449,710 | 202,432 | 1,328.8 | 812.9 | 150.8 |
| mldsa65 | 2 | 2 | yes | 2,208,425 | 470,490 | 212,384 | 1,470.3 | 902.3 | 159.8 |
| mldsa44 | 3 | 0 | yes | 1,587,666 | 330,654 | 219,548 | 1,231.1 | 766.6 | 134.8 |
| mldsa65 | 3 | 0 | yes | 1,751,129 | 338,698 | 230,172 | 1,375.4 | 863.4 | 144.8 |
| mldsa44 | 3 | 1 | yes | 2,188,135 | 470,787 | 221,548 | 1,284.9 | 799.8 | 143.0 |
| mldsa65 | 3 | 1 | yes | 2,410,576 | 492,110 | 232,948 | 1,434.6 | 905.5 | 152.5 |
| mldsa44 | 4 | 0 | yes | 1,642,397 | 367,947 | 218,708 | 1,148.3 | 699.9 | 126.9 |
| mldsa65 | 4 | 0 | yes | 1,805,553 | 377,432 | 227,852 | 1,297.4 | 801.8 | 136.3 |
| mldsa44 | 5 | 0 | yes | 1,694,042 | 400,547 | 220,324 | 1,116.6 | 673.7 | 122.2 |
| mldsa65 | 5 | 0 | yes | 1,857,801 | 407,448 | 230,188 | 1,264.5 | 774.9 | 132.1 |
| mldsa44 | 6 | 0 | yes | 1,745,884 | 434,414 | 221,500 | 1,091.7 | 658.8 | 120.0 |
| mldsa65 | 6 | 0 | yes | 1,906,467 | 439,112 | 233,524 | 1,241.6 | 756.3 | 129.4 |

## Circuit-size grid

Entries are exact zstd-22 compressed LFC2 bytes. Column = regular slice period; row = maximum plucker width. The full CSV also contains raw LFC1/LFC2, zstd-16/22, wires, terms, layers, input count, delta/segment/token counts, proof witnesses/constraints/block geometry, all timing medians and actual peak RSS.

### mldsa44, round 0 ordinary

| Max bits | 1 | 2 | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 215,054 | 383,586 | 513,173 | 640,360 | 795,243 | 890,331 |
| 1 | 329,588 | 485,318 | 607,791 | 717,916 | 861,699 | 962,465 |
| 2 | 367,545 | 522,396 | 642,746 | 754,930 | 908,498 | 1,002,267 |
| 3 | 511,097 | 657,851 | 763,132 | 873,052 | 1,017,247 | 1,120,496 |
| 4 | 419,296 | 571,254 | 691,531 | 797,462 | 945,284 | 1,048,502 |
| 5 | 473,603 | 622,923 | 725,017 | 827,798 | 973,697 | 1,072,852 |
| 6 | 511,274 | 667,579 | 769,770 | 869,919 | 1,015,325 | 1,107,287 |

### mldsa44, round 0 special

| Max bits | 1 | 2 | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 215,054 | 277,253 | 330,654 | 367,947 | 400,547 | 434,414 |
| 1 | 329,588 | 406,497 | 470,787 | 497,509 | 531,550 | 566,362 |
| 2 | 367,545 | 449,710 | 509,533 | 535,841 | 571,222 | 607,060 |
| 3 | 511,097 | 577,587 | 632,836 | 656,106 | 688,910 | 718,961 |
| 4 | 419,296 | 494,326 | 553,636 | 582,632 | 623,295 | 649,302 |
| 5 | 473,603 | 538,032 | 592,302 | 614,693 | 654,185 | 673,706 |
| 6 | 511,274 | 574,154 | 621,372 | 649,768 | 682,635 | 705,610 |

### mldsa65, round 0 ordinary

| Max bits | 1 | 2 | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 225,163 | 389,687 | 521,811 | 648,158 | 805,174 | 899,949 |
| 1 | 344,500 | 504,177 | 622,743 | 734,147 | 880,701 | 979,856 |
| 2 | 391,946 | 541,661 | 662,062 | 771,751 | 917,795 | 1,015,124 |
| 3 | 523,283 | 666,278 | 774,371 | 880,455 | 1,025,318 | 1,124,113 |
| 4 | 451,078 | 600,908 | 723,349 | 827,087 | 977,383 | 1,081,546 |
| 5 | 514,689 | 665,038 | 763,944 | 864,890 | 1,012,006 | 1,112,791 |
| 6 | 554,496 | 712,297 | 810,569 | 909,238 | 1,058,284 | 1,149,098 |

### mldsa65, round 0 special

| Max bits | 1 | 2 | 3 | 4 | 5 | 6 |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 225,163 | 286,414 | 338,698 | 377,432 | 407,448 | 439,112 |
| 1 | 344,500 | 423,246 | 492,110 | 519,479 | 553,249 | 580,161 |
| 2 | 391,946 | 470,490 | 533,187 | 558,788 | 595,435 | 628,790 |
| 3 | 523,283 | 590,656 | 642,687 | 665,087 | 700,926 | 729,175 |
| 4 | 451,078 | 528,100 | 591,822 | 617,954 | 657,273 | 683,920 |
| 5 | 514,689 | 581,188 | 635,804 | 657,325 | 695,367 | 715,950 |
| 6 | 554,496 | 615,082 | 664,868 | 689,237 | 723,147 | 750,677 |

## Geometry of selected settings

| Circuit | Period | Max bits | Special | Input wires | Total wires | Terms | Layers | Delta-table entries (sum) |
|---|---:|---:|:---:|---:|---:|---:|---:|---:|
| mldsa44 | 4 | 0 | 1 | 166,672 | 3,613,574 | 6,691,580 | 24 | 49,849 |
| mldsa65 | 4 | 0 | 1 | 194,663 | 3,791,554 | 8,064,583 | 24 | 51,169 |
| mldsa44 | 6 | 0 | 0 | 128,272 | 3,577,829 | 6,580,787 | 37 | 171,820 |
| mldsa65 | 6 | 0 | 0 | 156,263 | 3,756,007 | 7,953,988 | 37 | 166,683 |
| mldsa44 | 6 | 0 | 1 | 141,072 | 3,587,986 | 6,615,960 | 36 | 66,169 |
| mldsa65 | 6 | 0 | 1 | 169,063 | 3,765,966 | 7,988,963 | 36 | 67,489 |
| mldsa44 | 1 | 4 | 0 | 153,872 | 5,991,491 | 15,615,181 | 12 | 54,646 |
| mldsa65 | 1 | 4 | 0 | 181,863 | 6,161,098 | 16,993,279 | 12 | 62,344 |
| mldsa44 | 1 | 0 | 0 | 384,272 | 3,838,977 | 7,342,255 | 11 | 17,562 |
| mldsa65 | 1 | 0 | 0 | 412,263 | 4,015,597 | 8,713,898 | 11 | 18,879 |

## Interpretation

Packing reduces SHAKE state inputs from 1,600 per cut/permutation to 25×ceil(64/width). There are eight SHAKE permutations in each fixture. Its cost is the plucker's interpolation and range polynomials: the latter has degree 2^width, so larger widths can increase terms and depth substantially. Balancing avoids one anomalously small final decoder without changing the number of witnesses. All state computation remains in the XOR basis; this is an input encoding experiment, not a change of SHAKE basis.

Proof byte counts need not vary monotonically with width or period: they depend on both witness count and circuit depth, with discrete block-size choices by the existing geometry optimizer. Round-0 slicing trades another witness boundary for more uniform later SHAKE chunks. Overrides of the selected period-4 / special-round-0 / no-plucker default remain opt-in in the experimental MLDSA module. The requested full-subfield boundary and compact field serialization also apply to default MLDSA builds; mdoc and the production reader's default resource limits are unchanged.

## Effect of the corrected assumptions

For period 6 / unpacked XOR witnesses / special round 0, the previous measured proof sizes (boundary 0, 24/4-byte encoding) were 694,424 bytes for MLDSA-44 and 759,256 bytes for MLDSA-65. The new measured sizes are 221,500 and 233,524 bytes respectively. This is the combined effect of the correct subfield metadata, compact field encoding and geometry selected with those byte sizes; it is not a wire/term reduction. See the [previous experiment](FIRST_ROUND_SLICE_REPORT.md) for the historical measurements.

## Validation and artifacts

- All 84 schedule/packing combinations passed the three SHAKE tests (252 tests), including compiled witness acceptance and valid-point corruption rejection. Packed cases also reject the excluded lookup point.
- All 54 non-ignored MLDSA tests passed at balanced width 6 / period 6 / special round 0; all 42 ordering tests passed. Compact serialization tests cover exact bytes, all coefficients, malformed lengths and nonzero word padding.
- At grid measurement time, four default-build schedule/packing tests passed with deliberately conflicting experiment environment variables using the then-default unpacked period 6. The selected default was changed afterward to period 4 with a special round-0 cut and no pluckers.
- After selecting the new default, all 54 non-ignored MLDSA tests, four schedule/packing tests (with conflicting environment variables), and both full C++-vector circuit evaluations passed. Fresh default builds of both circuits are byte-identical to the saved p4-b0-r1 source.lfc2 grid artifacts. The no-default-features library check also passed.
- Workspace all-target/all-feature cargo check passed.
- All 14 core-proto tests passed, including default-reader budget and exact/lowered budget checks for both LFC1 and LFC2.
- LFC2 reorder preserves each circuit's term multiset under internal-wire renaming; inputs and outputs are fixed. Every saved LFC2 is decoded, byte-round-tripped and circuit-ID checked.
- 168 × (five timing flows + one fresh-memory flow) = 1,008 successful proof/verifier flows.

The [artifact audit](results/plucker-sf18/audit.json) verifies complete coverage, the input-count formula, all configured boundaries, proof byte counts, and exact source/circuit/proof equality for all 14 period-1 flag pairs. All 101 available old/new comparisons retain the same inputs, wires, terms, layers and delta-table counts. Eleven oversized cells need the explicit higher reader budget; none is a shared under-500-KB candidate.

[Full grid](results/plucker-sf18/plucker-grid-summary.csv) · [Every timing sample](results/plucker-sf18/plucker-grid-timings.csv) · [Runner](run_plucker_grid.py) · [Report generator](summarize_plucker_grid.py) · [Auditor](audit_plucker_grid.py)

Raw per-cell logs, proofs and LFC2 artifacts: `target/plucker-grid-sf18/p{period}-b{bits}-r{first}/{dataset}/`. Run `run_plucker_grid.py compile`, then `measure`, then this report generator. The runner accepts explicit release test binary paths; build with `--features mldsa-slicing-experiment` first. Use a new artifact root after changing the implementation; successful cells are otherwise reused.
