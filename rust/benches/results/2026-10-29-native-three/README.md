# Native three-stream LFC3: NEXT and ML-DSA

Baseline measurements before the private sumcheck split. The
[current report](../2026-10-29-layer-split/README.md) uses the same stored circuits
with eleven private working streams per sumcheck layer.

The compiler, LFC3 reader/writer, circuit identity and sumcheck now use quadratic, linear and constant streams directly. Quadratic and linear streams retain zero-coefficient assertion markers inline. No conversion or coefficient-policy selector remains. Nonzero coefficients, including +1 and -1, use ordinary arithmetic in the same streams.

Coefficient indices 0, 1 and 2 are fixed to zero, one and minus one. None of these values is serialized. Binary fields still initialize slot 2 to one, but all one/minus-one terms reference slot 1. Additional constants start at index 3. Compression preserves this prefix. LFA2 and the NEXT input manifest are unchanged; the local cache tag is MDOCNEXT5. The native identity domain is LFC3-v2-three-streams-v1. The retired eleven-stream draft is unsupported.

## Circuit storage

Exact bytes, zstd level 16. NEXT is the complete LFA2 signature/hash/manifest bundle, excluding the local cache wrapper. ML-DSA is an individual LFC3 circuit. Decoded heap counts owned capacities, including compressed dictionary records, segment/token vectors, coefficient tables and layer records. It is distinct from serialized uncompressed size and from total prover working memory.

| Circuit | Raw bytes | Zstd bytes | Decoded heap bytes |
|---|---:|---:|---:|
| next-2 | 647225 | 173660 | 2248600 |
| next-4 | 672470 | 174989 | 2338580 |
| mldsa-44 | 1695926 | 505570 | 5209004 |
| mldsa-65 | 1879258 | 518948 | 5690584 |

## Online proving and verification

Median of seven samples following a warmup, single thread pinned to CPU 2, AMD Ryzen 9 9950X, Rust 1.99.1, native release build with LTO and CPU boost disabled. Application order rotates and reverses across repetitions. Builds, offline circuit preparation and regression tests finished before the timing run. Allocation tracking is disabled for timing and enabled in separate memory executables. All 28 timed proofs verified.

Times include circuit decoding, witness/public-input preparation, commitment, proving/verifying, proof codecs and cleanup. NEXT also includes archive decompression. ML-DSA loads memory-resident raw circuits and rejects a changed public key outside each successful verification timer. Compilation, disk I/O and parameter selection are offline.

| Circuit | Prover ms | Verifier ms | Proof bytes | Prover peak MiB | Verifier peak MiB |
|---|---:|---:|---:|---:|---:|
| next-2 | 177.672 | 94.046 | 185576 | 42.646 | 34.280 |
| next-4 | 192.267 | 99.488 | 187240 | 47.502 | 37.359 |
| mldsa-44 | 688.805 | 327.318 | 178964 | 101.341 | 36.594 |
| mldsa-65 | 786.656 | 375.367 | 188180 | 106.321 | 40.815 |

Peak heap is the additional live requested allocation during each online call, not RSS. Serialized circuits and fixtures already resident before the call are excluded; circuit decoding and all new working allocations during the call are included. The verifier's already-resident serialized proof is outside its call baseline. Exact bytes are in memory.csv.

## Expanded terms

The value breakdown below describes coefficients within the three streams; these columns do not represent separate storage classes. The signature circuit is shared by both NEXT attribute counts. Binary minus-one terms count under +1.

| Circuit / component | Stream | Assertions | +1 | -1 | Other |
|---|---|---:|---:|---:|---:|
| next-2 / signature | quadratic | 0 | 66770 | 6950 | 68118 |
| next-2 / signature | linear | 3958 | 83725 | 864 | 11878 |
| next-2 / signature | constant | 0 | 33080 | 10 | 1108 |
| next-2 / hash | quadratic | 9921 | 1329270 | 0 | 482479 |
| next-2 / hash | linear | 8777 | 223218 | 0 | 1330608 |
| next-2 / hash | constant | 0 | 790911 | 0 | 203 |
| next-4 / signature | quadratic | 0 | 66770 | 6950 | 68118 |
| next-4 / signature | linear | 3958 | 83725 | 864 | 11878 |
| next-4 / signature | constant | 0 | 33080 | 10 | 1108 |
| next-4 / hash | quadratic | 12475 | 1573240 | 0 | 526147 |
| next-4 / hash | linear | 9739 | 255420 | 0 | 1451668 |
| next-4 / hash | constant | 0 | 862291 | 0 | 307 |
| mldsa-44 / verifier | quadratic | 1042 | 1513245 | 117963 | 2023851 |
| mldsa-44 / verifier | linear | 181151 | 1947053 | 76124 | 702641 |
| mldsa-44 / verifier | constant | 0 | 31595 | 90634 | 5216 |
| mldsa-65 / verifier | quadratic | 4372 | 1562362 | 144973 | 3081363 |
| mldsa-65 / verifier | linear | 205183 | 2040319 | 94561 | 790236 |
| mldsa-65 / verifier | constant | 0 | 38653 | 91142 | 7024 |

## Audit and validation

Authenticated metadata inspection checks every newly generated circuit ID and verifies that inputs, public inputs, outputs, wires, layers and expanded term counts match the eleven-stream HEAD baseline d8f000f exactly. The proof protocol, rounds and witness layout are unchanged. New circuit IDs change Fiat–Shamir queries, so proof-byte differences reflect changed query/Merkle-path overlap rather than a change in rounds.

Cleanup removed the class-policy APIs and environment selectors, coordinate-only record types, fixed-coefficient containers, eight additional streams, legacy experimental affine/optional containers, and stale One-wire exemptions from the v2 compiler. Native layers contain three explicit owned streams and two derived assertion counts. The shared compiler IR still represents literal constants; no circuit input or runtime-supplied One wire is emitted. V2 monomial weights remain iterative. Test-only fixture builders for old handwritten quadratic tensors are isolated from production; there is no serialized legacy conversion path.

The full suite passed 500 tests, including native ML-DSA acceptance/corruption, NEXT two/four-attribute proofs, all v1 saved-proof bytes and frozen circuit-ID/serialization checks. A separate new binary-slot reader regression passed, for 501 passing checks in total. The unrelated pre-existing untracked streaming.rs source-inventory issue is still excluded. The v1 compiler and numerical runtime sources are untouched; removal of unused shared experimental storage is covered by the frozen compatibility checks. Compiler-, prover-, and verifier-only builds and the all-target experimental check pass.

Reader tests cover exact implicit values, binary slot-2 rejection, no serialized reserved constants, duplicate reserved-value rejection without ID enforcement, index and coordinate bounds, truncated files, fragmented reads, tampered identities and whole-circuit term budgets. Sumcheck tests cover independent quadratic/linear assertions even with zero outgoing weights, scalar/no-round cases, general/unit/negative coefficients and bad witnesses over prime, binary and sextic fields. Existing witness-value-free diagnostic messages are retained.

## Reproduction

From rust/:

```sh
cargo build --release --bench mdoc_zk_bench_next --bench mldsa_bench_v2 --features testonly,experimental
rustc --edition=2021 -O benches/results/2026-10-29-native-three/run.rs -o /tmp/native-three-run
/tmp/native-three-run stage-time
/tmp/native-three-run prepare
# Rebuild with bench-memory, then:
/tmp/native-three-run stage-memory
/tmp/native-three-run memory
/tmp/native-three-run time
```

[run.rs](run.rs) stages binaries from rust/target/release/deps and retains fresh caches and logs under /tmp/native-three-benchmark. Timing and heap executables are separate. The timing phase uses only saved circuits. Run it after preparation, builds and tests are idle. [metadata.rs](metadata.rs), linked against the release library, authenticates circuits, checks unchanged geometry against the preceding report and emits structure/size CSVs. These Rust tools use local workspace paths; adjust constants if relocating the checkout.

Raw data: [timing samples](samples.csv), [medians](medians.csv), [sizes](sizes.csv), [heap](memory.csv), [geometry](geometry.csv), [term breakdown/dictionaries](terms.csv). The [eleven-stream measurements](../2026-10-29-next-v9/README.md) are historical, from d8f000f.
