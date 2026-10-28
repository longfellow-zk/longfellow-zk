# MLDSA packed commitment, 2026-10-28

Median of three runs per circuit and implementation, on one Ryzen 9 9950X
thread pinned to CPU 2, boost disabled. Native release build; allocation
tracking disabled. Online timings include circuit decoding, input/witness
preparation, initialization, commitment, proving/verification, serialization
and cleanup. Inputs are memory resident. Offline compilation and parameter
selection are excluded. Both implementations use k=1024, s=25, n=4096, t=128.

| Circuit | Commitment path | Prover ms | Verifier ms | Proof bytes |
|---|---|---:|---:|---:|
| MLDSA-44 | Ambient, unpacked | 1097.220 | 620.307 | 523830 |
| MLDSA-44 | Generic sextic packing | 896.823 | 427.414 | 178868 |
| MLDSA-65 | Ambient, unpacked | 1279.113 | 715.913 | 583638 |
| MLDSA-65 | Generic sextic packing | 1030.489 | 491.119 | 187412 |

Packing reduces prover time by 18.3% / 19.4%, verifier time by 31.1% / 31.4%,
and proof size by 65.9% / 67.9%, respectively. All twelve proofs verified and
all twelve changed-public-key checks rejected.

The [historical MLDSA-44 proof](historical-subfield-44.log) using the old backend
subfield encoding was 178338 bytes. The new packed proof is 530 bytes larger
(0.30%). That historical format differs from both ambient-only implementations compared above; its
proof size is a reference, not a newly rerun timing comparison.

## Witness and circuit

The witness generator and circuit are unchanged. The packing integration
accepts ordinary ambient-field inputs, verifies that private inputs lie in
the prime field, and packs six per sextic word before commitment. The original
GKR pads/products follow, then seven packing cells. Public inputs are
substituted into the final affine claim.

| Circuit | Private inputs | Packed words | GKR pad cells | Packing cells | Total committed cells |
|---|---:|---:|---:|---:|---:|
| MLDSA-44 | 161551 | 26926 | 912 | 7 | 27845 |
| MLDSA-65 | 185446 | 30908 | 912 | 7 | 31827 |

Each parameter set has identical circuit geometry and LFC2 bytes in the two
runs. LFC2 SHA-256:

- MLDSA-44: `17abe7bc76f5e2873ced7bcb7c0fa6ab200b8e33523dba331c1fa0a7f782ec4a`
- MLDSA-65: `6e8acba621188a398b7ef2a836c53e076fc95064276e484329817bb16dd9294e`

The new LFM1 envelope includes six trace-zero responses U and A (126 bytes)
and the ambient-only PLG8 backend proof. Both native packing equations are
authenticated against the original packed commitment. The specification and
sampling functions were not changed for this integration.

## Reproduction and validation

From the Rust workspace:

```sh
cargo bench --bench mldsa_bench_v2 --features experimental,testonly --no-run
MLDSA_BENCH_REPEATS=3 taskset -c 2 \
  target/release/deps/mldsa_bench_v2-61ee897a1fe800ff all
```

The executable suffix may differ between builds. The unpacked executable was
saved as `/tmp/mldsa-v2-unpacked-before-packing` before replacing the benchmark
entry point; it has the same corrected three-byte coefficient sampler and
ambient-only backend. It was rerun immediately before the packed executable.
Raw measurements are in [unpacked.log](unpacked.log) and [packed.log](packed.log).

Validation covers generic packing, both native equations in the actual
Polygero matrix, proof round trips, adversarial edits and canonical decoding,
ordinary v2 and GF128 packed regressions, module dependencies, all-target
checking, clippy, and separate prover/verifier/compiler/data feature builds.
This experiment does not establish a composed Fiat–Shamir security bound,
joint zero-knowledge simulation, or a formal Rust refinement; see the
[implementation audit](../../../runtime/dual-packing/AUDIT.md).
