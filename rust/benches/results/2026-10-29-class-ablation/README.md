# Circuit class ablation: mdoc v9 and ML-DSA

Historical measurements from the retired eleven-stream implementation.
Current native three-stream results are in the [latest report](../2026-10-29-native-three/README.md).
Reproducing these historical layouts requires the original source revision;
commit d8f000f contains the eleven-stream LFC3 implementation.

## Retained implementation

The final implementation keeps all eleven concrete streams and uses `{0,1,-1}`
by default for both applications. It retains the explicit coefficient-policy API
and all benchmark cases for reproducing the comparisons. The measurements below
precede the source cleanup and LFC3 format finalization. The arithmetic loops are
retained. Current compilation emits native LFC3 streams inside LFA2; the old experimental
artifacts require the preserved historical benchmark binaries.

## Original recommendation from the measurements

1. Keep v2 quadratic, linear, and constant streams, with no One input. Constants remain public affine offsets; ignoring their coefficient classes does not mean dropping constant terms.
2. Keep quadratic and linear assertions (`0`) separate. Zero is an assertion marker with different semantics from an ordinary arithmetic coefficient.
3. Use `{0,1}` as the general default and for mdoc. Unit streams deliver the substantial controlled speedup. Adding minus-one streams to mdoc gives mixed end-to-end timings and slightly larger uncompressed bundles.
4. Use `{0,1,-1}` for ML-DSA when optimizing proving time: it has the best median here and improves raw/zstd sizes over `{0,1}`. Treat the incremental speed advantage as small; the storage improvement is more decisive.
5. Retain `{0}` as a transport-oriented ML-DSA option only if a roughly 2-3% zstd saving over the full split outweighs a 13-14% prover slowdown. Its online memory saving is only about 43-52 KB. Do not use `-1` streams without `1` streams as the default.
6. Select the policy at offline circuit compilation and authenticate it in the circuit format. Keep runtime loops explicit and free of per-term minus-one tests. Preserve the historical unified backend only as a reference, rather than reintroducing it into the v2 runtime.

## Method and interpretation

AMD Ryzen 9 9950X, native release build, Rust 1.99.1, boost disabled, one thread pinned to CPU 2. Each application has one warmup per variant and seven timed samples, rotating and reversing variant order between repetitions. Preparation/compilation ran separately. Every measured proof verified; ML-DSA also rejected a changed public key outside its successful-operation timers.

The four modern policies `{0}`, `{0,1}`, `{0,-1}`, `{0,1,-1}` use the same compiler, graph, witness, degree separation, assertion lowering, proof protocol, and runtime binary. Their only change is coefficient partitioning. Authenticated geometry inspection confirms identical inputs, public inputs, outputs, wires, layers and expanded-term counts for these policies.

Historical unified and degree-only references were built from HEAD `e673d05` in a separate checkout. They also differ in memory representation, assertion lowering and inline coefficient shortcuts. The unified reference additionally has a One wire. These rows measure implementation packages, not an isolated causal effect of a single class. `0` extraction cannot be attributed independently from these reference rows.

`{0,-1}` leaves literal one coefficients general. In characteristic two, minus one equals one; its distinct minus-one class is disabled, so the mdoc hash component matches `{0}`. mdoc's signature circuit is over P256 and is shared between 2 and 4 attributes. ML-DSA uses the native 24-bit-prime extension field, not binary emulation.

Times include circuit decoding, input/witness construction, commitment, proving/verifying, proof codecs and cleanup. v9 includes zstd decoding; ML-DSA reads raw circuits. Message and signature fixtures match across variants. Parameter selection is offline.

## Prover / verifier medians (ms)

| Layout | mdoc-2 | mdoc-4 | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|---:|---:|
| Historical unified | 183.706 / 93.465 | 197.943 / 99.147 | 830.806 / 386.423 | 971.125 / 452.013 |
| Historical degree-only | 170.249 / 91.581 | 184.592 / 98.202 | 748.845 / 362.081 | 882.268 / 425.026 |
| Degree + {0} | 179.292 / 97.657 | 194.296 / 103.916 | 669.561 / 322.203 | 769.231 / 367.911 |
| Degree + {0,1} | 159.876 / 89.411 | 174.025 / 94.547 | 582.445 / 289.749 | 676.464 / 335.034 |
| Degree + {0,-1} | 178.927 / 97.547 | 195.149 / 103.763 | 664.230 / 320.603 | 762.028 / 367.845 |
| Degree + {0,1,-1} | 160.172 / 89.187 | 173.316 / 94.789 | 575.937 / 287.004 | 671.348 / 332.139 |

## Raw / zstd circuit bytes

zstd level 16. mdoc includes hash, signature and manifest, excluding the cache wrapper.

| Layout | mdoc-2 | mdoc-4 | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|---:|---:|
| Historical unified | 675774 / 176134 | 695394 / 176756 | 1732146 / 508205 | 1972268 / 542487 |
| Historical degree-only | 650271 / 177355 | 675481 / 177705 | 1675158 / 504616 | 1860330 / 520872 |
| Degree + {0} | 647648 / 176642 | 674246 / 177451 | 1674271 / 503907 | 1866112 / 521056 |
| Degree + {0,1} | 574590 / 157611 | 593582 / 158615 | 1731719 / 541420 | 1927696 / 563659 |
| Degree + {0,-1} | 646884 / 176196 | 673482 / 176916 | 1675231 / 504450 | 1875379 / 527903 |
| Degree + {0,1,-1} | 575786 / 157396 | 594778 / 158280 | 1679297 / 515070 | 1869517 / 535991 |

## Decoded circuit heap bytes

| Layout | mdoc-2 | mdoc-4 | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|---:|---:|
| Historical unified | 2306680 | 2378228 | 5152316 | 5753532 |
| Historical degree-only | 2307024 | 2396852 | 5217092 | 5710104 |
| Degree + {0} | 2297040 | 2391512 | 5162412 | 5670280 |
| Degree + {0,1} | 2061820 | 2138548 | 5303236 | 5833296 |
| Degree + {0,-1} | 2295452 | 2389924 | 5190660 | 5730524 |
| Degree + {0,1,-1} | 2065300 | 2142028 | 5205464 | 5722184 |

## Prover / verifier peak additional heap (MiB)

Measured separately with allocation tracking, one successful online sample per variant. These are live requested allocations relative to the call's baseline, not RSS. Resident circuit bytes/fixtures are excluded. Serialized raw size, decoded storage and total prover memory are different quantities; working memory dominates.

| Layout | mdoc-2 | mdoc-4 | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|---:|---:|
| Historical unified | 42.702 / 34.336 | 47.540 / 37.397 | 101.335 / 38.806 | 106.506 / 42.583 |
| Historical degree-only | 42.702 / 34.336 | 47.558 / 37.415 | 101.373 / 38.867 | 106.440 / 42.540 |
| Degree + {0} | 42.692 / 34.326 | 47.552 / 37.410 | 101.297 / 36.549 | 106.302 / 40.796 |
| Degree + {0,1} | 42.468 / 34.102 | 47.311 / 37.168 | 101.431 / 36.684 | 106.458 / 40.951 |
| Degree + {0,-1} | 42.691 / 34.325 | 47.551 / 37.408 | 101.323 / 36.576 | 106.360 / 40.853 |
| Degree + {0,1,-1} | 42.471 / 34.105 | 47.315 / 37.172 | 101.338 / 36.590 | 106.352 / 40.845 |

## Proof bytes

All four controlled policies retain the same round/pad counts and commitment layout. Their circuit IDs differ, changing Fiat-Shamir queries and Merkle-path overlap; the small byte differences are not a reduction in protocol rounds.

| Layout | mdoc-2 | mdoc-4 | ML-DSA-44 | ML-DSA-65 |
|---|---:|---:|---:|---:|
| Historical unified | 184232 | 186824 | 178324 | 187668 |
| Historical degree-only | 185000 | 186472 | 178932 | 188148 |
| Degree + {0} | 184552 | 186984 | 178164 | 187636 |
| Degree + {0,1} | 185352 | 187144 | 178868 | 187956 |
| Degree + {0,-1} | 184296 | 186408 | 179092 | 187828 |
| Degree + {0,1,-1} | 185000 | 186760 | 178036 | 187444 |

## Counts and validation

[Geometry](geometry.csv) and [stored term-class counts](terms.csv) cover every component of all variants. `0` columns count serialized assertions; final zero-output checks remain implicit. The historical mixed layouts store their assertion markers in general streams. [Minus-one counts](minus-one-counts.csv) give expanded terms and dictionary entries for the canonical ML-DSA and mdoc signature circuits.

The class-policy tests exercise all four policies over prime, binary and extension fields, verify proofs and reject incorrect witnesses, authenticate archives, reject invalid masks and truncated archives, and assert unchanged graph geometry. 366 focused shared regression tests passed. The pre-existing untracked `streaming.rs` is preserved; its known source-inventory test was excluded. Default, compiler-only, prover-only and verifier-only checks are recorded separately.

## Reproduction and artifacts

The Rust [driver](run.rs) prepares each case, runs the rotated timing experiment and collects heap measurements. Historical binaries use `testonly,experimental` (unified) and `testonly,v2` (degree-only). The measured modern binaries used the preserved experiment feature set; `CIRCUIT_COEFFICIENT_CLASSES=zero|one|minus|all` selected the offline policy. Use separate caches for each case. Add `bench-memory` only for heap runs. Those binaries read assertion-stream experiment/signed-coefficient experiment/coefficient-policy experiment. The present runtime accepts LFC3 only, so reproducing these exact artifacts requires the preserved historical binaries.

```sh
cargo build --release --bench mdoc_zk_bench_v9 --bench mldsa_bench_v2 --features testonly,experimental
# Set CIRCUIT_COEFFICIENT_CLASSES and use a fresh MDOC_V9_CACHE / MLDSA_BENCH_SAVE_DIR.
# Once prepared, the driver pins samples to CPU 2 and loads the saved circuits.
rustc --edition=2021 -O run.rs -o run
./run prepare
./run time
# Rebuild all three binary families with bench-memory, then:
./run memory
```

The driver currently uses `/tmp/longfellow-ablation` as its root; adjust that constant or recreate its directory layout. Raw app logs, binaries and archives remain there. [All timing samples](samples.csv), [medians](medians.csv), [memory samples](memory.csv) and [combined exact metrics](summary.csv) accompany this report.
