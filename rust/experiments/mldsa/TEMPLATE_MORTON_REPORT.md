# Morton traversal after template-driven wire numbering

Release/native control on the saved selected circuits: MLDSA period 4, special
round 0, no pluckers, subfield boundary ninput, 18/3-byte serialization; mdoc v8
two-attribute hash and signature. No production source changes.

The existing `layer_template_order_sweep` harness reads each saved original or
template-driven circuit, applies `ORDER_COMPONENTS=6` (absolute Morton), and
rebuilds ordinary LFC2 with `ORDER_SEGMENTS=standard`. It preserves exact terms
and wire IDs relative to its input, verifies circuit IDs, and checks serialization
and exact term-stream roundtrips. Outputs and logs are retained under
`target/template-morton-control`.

## Result

Template-driven numbering does not transfer the selected MLDSA compression gains
to global Morton traversal. With the same stock segmenter, it makes Morton LFC2
28.97% larger for MLDSA-44 and 34.58% larger for MLDSA-65. The combined mdoc
Morton archive improves only 0.57%. No production policy is changed.

Exact whole-file zstd-22 bytes (standalone bulk compression except the jointly
compressed, streaming mdoc archive):

| Circuit | Original wires, shape/output traversal | Template wires, template traversal | Original wires, Morton | Template wires, Morton |
|---|---:|---:|---:|---:|
| MLDSA-44 | 470,899 | 367,947 | 2,490,683 | 3,212,294 |
| MLDSA-65 | 504,020 | 377,432 | 2,509,490 | 3,377,316 |
| mdoc signature | 63,398 | 58,669 | 123,747 | 124,969 |
| mdoc hash, two attributes | 100,969 | 99,356 | 178,431 | 174,970 |
| Combined mdoc LFA2 archive | 162,101 | 156,667 | 299,804 | 298,095 |

Raw LFC2 / LFA2 bytes, in the same column order:

| Circuit | Original shape/output | Template traversal | Original Morton | Template Morton |
|---|---:|---:|---:|---:|
| MLDSA-44 | 1,738,264 | 1,642,397 | 5,913,003 | 7,703,463 |
| MLDSA-65 | 1,978,323 | 1,805,553 | 5,940,701 | 8,134,309 |
| mdoc signature | 222,143 | 244,943 | 264,638 | 274,063 |
| mdoc hash | 548,467 | 543,913 | 709,175 | 699,579 |
| Combined mdoc archive | 770,782 | 789,028 | 973,985 | 973,814 |

Sum of layer-local distinct coordinate/coefficient delta counts:

| Circuit | Original shape/output | Template traversal | Original Morton | Template Morton |
|---|---:|---:|---:|---:|
| MLDSA-44 | 62,796 | 49,849 | 255,759 | 446,881 |
| MLDSA-65 | 67,007 | 51,169 | 260,369 | 486,434 |
| mdoc signature | 12,708 | 11,697 | 17,155 | 18,282 |
| mdoc hash | 18,210 | 18,051 | 22,237 | 21,982 |

The Morton LFC1 zstd-22 controls also regress under template numbering:
MLDSA-44 2,157,931 to 2,410,378; MLDSA-65 2,172,509 to 2,624,427 bytes.
Thus the negative result is not only an LFC2 segmenter effect.

These fresh Morton sizes supersede the earlier period-4 measurements with old
field serialization. Terms, layer widths, depth, original inputs, and witness
counts are unchanged. Sorting an already template-numbered file retains those
wire labels exactly. The earlier template-generation experiment checked the
internal-wire bijection against original numbering; this experiment checks exact
term-multiset preservation separately for each saved input.

## Segmentation and interpretation

Both Morton columns use precisely the same stock segmenter. Original hand-major
files also use stock segmentation; selected template traversal uses `reuse`.
Consequently the two Morton columns isolate numbering, while comparisons against
the selected template files include both traversal and segmentation effects.

The existing `reuse` routine expects template-instance spans recorded as runs.
The Morton control rebuilds each layer as one run, so there are no repeated run
interiors for that routine to reuse: it returns stock segmentation. It would not
be meaningful to claim a separate template-aware Morton result merely by enabling
that selector. Discovering new spans within Morton order would be a different
experiment, not part of this control.

The measured conclusion is that these wire labels are useful together with the
template traversal, not as a generally compression-optimal numbering. Morton
sorting breaks the intended repeated sequences and greatly increases distinct
deltas. This experiment does not by itself apportion the loss among translation
sensitivity, instance interleaving, and shared-port effects, or prove that every
possible Morton-compatible numbering must fail.

## Validation and proof implications

- Release/native builds; existing workspace native CPU flags. No C++ changes.
- All eight sorted files passed exact term-multiset, ID, serialization, and
  decoded term-stream checks in the existing ordering harness.
- A new experimental check exercised `HQuad::from_g_binding` and every alternating
  h0/h1 fold on all 178 stored layers, with deterministic sampled field challenges.
  Every result matched an independent direct sum using dense equality weights.
  This uses the actual round-major binder without runtime sorting.
- Four complete MLDSA round-major proofs (original/template numbering for both
  variants) were serialized, parsed, and verified. Proof bytes were respectively
  217,844 / 218,036 for MLDSA-44 and 228,460 / 228,204 for MLDSA-65. Witness counts
  remain 163,303 / 187,198, constraints 24, and encoded blocks 6,125 / 6,143.
- All four mdoc archive profiles passed application-level proving and verification.
  The mdoc application remains v8 hand-major even for Morton-stored circuits;
  its round-major compatibility is established by the separate per-layer checks,
  not by an end-to-end round-major mdoc application proof. Changing the spec to v7
  would also change witness/public-input semantics and is deliberately avoided.
- Circuit IDs and transcript challenges change. Equal geometry does not imply
  identical proof bytes because batched Merkle paths depend on challenges.
- Proof runs are one-flow correctness checks. Their times and process high-water
  marks in logs are diagnostic, not a new controlled speed/memory comparison.

## Reproduction and artifacts

Build:

```sh
cargo test --release -p circuits-experimental --features mldsa-slicing-experiment --test layer_templates --test template_proofs --test morton_folds --no-run
```

Run each phase `sizes`, `validate`, and `summary` using the emitted release paths:

```sh
python3 experiments/mldsa/run_template_morton.py sizes --orderer target/release/deps/layer_templates-ea9ecaff61fd5f69 --prover target/release/deps/template_proofs-1eba8861353003c4 --folds target/release/deps/morton_folds-270188b5b090fa0a
```

The runner resumes successful logs; use a clean artifact directory for changed
implementations. It retains `sizes.csv`, `archives.json`, binary/input/output
SHA-256 hashes, all eight Morton LFC2 files, four mdoc archives, MLDSA proofs,
and validation logs under `target/template-morton-control`. Archive byte counts
exclude the benchmark container prefix (32-byte trusted combined ID).
