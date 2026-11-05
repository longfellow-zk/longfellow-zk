# Longfellow V2: extraction and soundness

The `LfzkV2.Linear` namespace models Rust snapshot `21cb029`: native affine
sumcheck, binary input packing, linear-only Polygero, two Merkle commitments,
and the affine MAC. Its complete authenticated raw-proof endpoint is
[`Linear.Runtime.RawRuntimeExtraction.extraction_116`](LfzkV2/Linear/Runtime/RawRuntimeExtraction.lean).
The prior `LfzkV2.Native`/`LfzkV2.Packed` product-checked snapshot `fcf8a3a`
and its 117-bit certificate are retained unchanged.

## Randomized linear terminal

Four ordinary pad cells `pA,pB,pAB,pD` are committed. After the rounds, the
prover sends `d`, receives a nonzero scale `r`, sends `mA,mB`, then receives
`alpha`. The verifier emits only the affine row

```text
C + r*(d+pD) + r²*pAB - mA*mB = 0
```

and carries `mA+alpha*mB-r*pA-alpha*r*pB-alpha*L(u)` to the next layer.
Honest construction uses `pAB=pA*pB`; soundness allows arbitrary `pAB`.
A false claim leaves a fixed nonzero quadratic in `r`, hence an additional
`2/(|F|-1)` per layer. The round and combination losses are unchanged.
The new frontend replay proves the required message order and causality.

[`Linear.Runtime.CompiledFS`](LfzkV2/Linear/Runtime/CompiledFS.lean) proves
both actual compiler transfers. Its instances have `nq=0`, reuse the shared
Polygero analysis, and require no product-copy checks. The direct input path
has no packing stage; the packed path uses the same trace check and two
affine adapter rows. The complete authenticated bound, including the MAC and
both Merkle terms, is proved in
[`Linear.Runtime.RawExtraction`](LfzkV2/Linear/Runtime/RawExtraction.lean).

For the geometry and candidate lists below, the conservative annotated cost
is `(925*N+19303)/2^128+21661/2^255`. Raw replay replaces `N` with `N+1`.
There are at most 1205 verifier challenge slots, with 20 hash layers and
21 signature layers. The exact normalized cost retains the nonzero-field
denominators; the rounded certificate uses `2/(q-1) <= 4/q`. The all-budget
result is `(1+N+tA)/2^116`, rather than reusing the old numerical certificate.
See the [audit](../AUDIT.md) for the exact finite bound and explicit premises.

The sumcheck messages use `2*rounds+3*layers` field elements and the pad plan
uses `2*rounds+4*layers`, proved in [`Linear.Sizes`](LfzkV2/Linear/Sizes.lean).
The honest terminal masking bijection is proved for nonzero `r`; complete
joint zero knowledge is not asserted.

## Retained product-checked checkpoint

The following detailed tables describe the unchanged `fcf8a3a` model.
Shared native circuit semantics, packing identities, geometries, MAC, and
Merkle results are also used by the linear-terminal composition above.

The model separates protocol soundness from implementation correspondence.
It proves extraction for the mathematical verifier under the explicit field,
sampler, geometry, and circuit premises below; it does not verify Rust source
execution or concrete hash implementations.

## Native affine frontend

The circuit has independent quadratic, linear, and constant streams, with
separate linear and quadratic assertion occurrences. For effective streams
`Q,L,K`, the prover binds `q = Q*W+L` and begins the rounds with `C-K`.
The final claims are `A=W(u)` and `B=q(u)`. The next weights use `Q`, and the
next claim is `A+alpha*(B-L(u))`. Both corrections are reconstructed from the
trusted circuit and earlier challenges.

| Result | Endpoint |
|---|---|
| Affine layer completeness and soundness over any field | [`SumcheckV2.affine_layer_completeness`, `affine_layer_reduction`](../sumcheck-v2/SumcheckV2/Affine.lean) |
| Three-stream truth, including invalid assertions | [`Native.CircuitLayer.effective_truth`](LfzkV2/Native/Circuit.lean) |
| Corrected builder, malformed-length rejection, fixed product slots, and sparse lowering | [`Native.buildConstraints_correct`, `compiled_iff_clear`](LfzkV2/Native/Constraints.lean) |
| Circuit soundness and honest masked construction | [`Native.Circuit.soundness_reduction`](LfzkV2/Native/Soundness.lean), [`prove_complete`](LfzkV2/Native/Prover.lean) |
| Challenge tests and sharp budget | [`Native.Circuit.tests_soundness`, `tests_budget_le_sharp`](LfzkV2/Native/Events.lean) |
| Native prefix reconstruction and causal hash-point data | [`Native.Replay.semantic_bad_of_accepts`](LfzkV2/Native/SemanticReplay.lean), [`pointData_eq`](LfzkV2/Native/HashReplay.lean) |

The projective round identity is `C=c0+c2`, followed by
`z²*C+(1-z²)*c0+z*c1`. Its bad-event bound is two field values per round,
one per final combination, and at most one per layer's assertion batch.
The sharp frontend budget is
`logv + sum_layers(min(1, assertions) + 2*logw + 1)`.
The affine corrections add no challenge slots. Scalar layers, empty chains,
and repeated assertion occurrences are included.

The native replay reuses the earlier model's message geometry through
`Circuit.shape`. This is only a schedule projection: all claims, true
polynomials, corrections, and bad-event semantics use the native circuit.

## Packed inputs and the compiled backend

[Dual packing](../dual-packing/README.md) supplies the field-basis and
trace-pairing identities. The adapter's source equation is the native
frontend's final input claim, after subtracting the public-input contribution.
Each committed packed word has canonical base-field coordinates. Over
`GF(2)`, every extracted private coordinate is a bit, even for an adversarial
committed word; unused trailing coordinates have coefficient zero.

The verifier checks that each coordinate of `U` has zero trace. It then samples
the packing vector challenge, receives the scalar response `A`, and supplies
two affine equations to Polygero. `A` and the later backend response are absent
from the packing challenge's prefix. A false source equation pays at most
one field inverse per committed candidate. Degree-one inputs retain the
original source row and add no packing challenge. Their unused scalar in the
common abstract carrier is the constant-zero annotation of the direct codec;
allowing other annotations in the theorem is conservative.

| Result | Endpoint |
|---|---|
| Exact two-row lowering and backend extraction | [`Packed.Statement.rows_iff_native`, `satisfies_rows`](LfzkV2/Packed/Backend.lean) |
| Source-claim equality, native frontend transfer, and binary coordinates | [`source_claim_iff`, `frontend_or_bad`, `unpack_binary_bit`](LfzkV2/Packed/Inputs.lean) |
| Fixed-candidate and sampled candidate-family packing bounds | [`Packed.Statement.sampled_candidates_card_le`](LfzkV2/Packed/Counting.lean) |
| Actual packed and direct compiler instances | [`Packed.Compiled.side`, `Packed.Direct.side`](LfzkV2/Packed/CompiledFS.lean) |
| Instances with certified geometry and terminal potentials | [`profiledSide`](LfzkV2/Packed/ProfiledSide.lean) |

The compiler transfer follows from the emitted rows and the native source
identity; it is not a soundness premise supplied to the composed endpoint.
Product consistency remains an independent backend constraint in this
snapshot. The API checks include an assignment whose affine rows pass while
its product check and clear verifier reject.

## Authenticated extraction

The composition uses one adaptive transcript oracle. Both commitment roots
are fixed before the MAC challenge. The hash proof comes first, and the
signature proof's context contains that complete transcript, including its
packing and backend responses. Each adaptive query pays the maximum local
budget across the MAC and both sides.

The extractor searches the two fixed committed candidate lists. A returned
pair satisfies both native circuit predicates and has equal common messages.
The MAC row identities are checked separately for each side, so their private
additive blinds need not agree.

| Result | Endpoint |
|---|---|
| Native frontend, packing, and graded Polygero charge on one staged oracle | [`Packed.FiatShamir.event_soundness_le`](LfzkV2/Packed/FiatShamir.lean) |
| Two-field paired extraction and shared adaptive-query bound | [`Packed.TwoFieldPotential.extract_valid`](LfzkV2/Packed/TwoFieldPotential.lean), [`TwoFieldFS.extraction_le`](LfzkV2/Packed/TwoFieldFS.lean) |
| Both Merkle opening checks, common cut-trace extraction, and context invariance | [`Packed.TwoFieldCommitmentFS.extraction_le`](LfzkV2/Packed/TwoFieldCommitmentFS.lean) |
| Verifier-recomputed MAC answer and raw acceptance probability | [`Packed.RawExtraction.key_coherent`, `probability_le`](LfzkV2/Packed/RawExtraction.lean) |
| All-budget numerical extraction bound | [`Packed.RawRuntimeExtraction.extraction_117`](LfzkV2/Packed/RawRuntimeExtraction.lean) |

The numerical endpoint bounds
`Pr[accept and paired extraction fails] <= (1+N+tA)/2^117`, where `N` counts
adversarial transcript queries and `tA` counts adversarial Merkle-hash queries.
It allows arbitrary query order, recommitment, grinding, and adaptive proof
selection. The raw acceptance event has no supplied-MAC-answer coherence
premise: verifier replay derives the answer.

## Geometry and numerical accounting

| Side | `n` | `k` | `s` | Openings | Analysis cutoff | Candidate bound |
|---|---:|---:|---:|---:|---:|---:|
| Hash | 2912 | 416 | 15 | 86 | 1136 | 25 |
| Signature | 2912 | 416 | 15 | 86 | 1127 | 33 |

The list cutoffs are analysis choices, not protocol changes. The hash-side
packing charge is `25/|F_hash|`; the shared MAC charge is at most
`25*33/|F_mac|`. With the stated field sizes and frontend bounds, the exact
normalized annotated field/MAC cost is at most

```text
(925*N + 17303)/2^128 + 18889/2^255.
```

Raw verifier replay replaces `N` by `N+1`. The numerical theorem also includes
both Merkle explanation errors, with at most 1164 verifier challenge slots
and 11648 Merkle checking queries. Eight adversarial Merkle queries cover the
startup cost; below that threshold, authenticated acceptance already requires
a digest guess. This small-budget argument needs no numbered-leaf assumption.

The [profiles](LfzkV2/Packed/RuntimeProfiles.lean),
[cost normalization](LfzkV2/Packed/RuntimeCost.lean), and
[numerical comparison](LfzkV2/Packed/RuntimeSecurity.lean) are kernel checked.
The source geometry bounds are exposed as premises rather than inferred from
unverified Rust metadata.

## Assumptions and implementation boundary

The theorem retains explicit premises for:

- The geometries above, distinct evaluation points, and the Polygero
  decoder and column encodings.
- Hash and MAC fields of size at least `2^128`, a signature field of size
  at least `2^255`, and a Merkle digest alphabet of size exactly `2^256`.
- Balanced samplers for frontend blocks, packing vectors, backend coins,
  query sets, and the MAC key on one common ideal transcript alphabet.
- Trusted native circuits, basis and input embeddings, pad and product
  layouts, public inputs, and each circuit's MAC row identity.
- Output dimensions at most 5 and 3, with frontend budgets at most 593 and
  565; the checked round/layer bounds imply those budgets.
- Merkle codecs, role decoders, and enough answer tape:
  `TM >= tA+11648`.

Identifying Rust circuit data, byte-level transcript encodings, parser behavior,
field arithmetic, allocation bounds, and SHA/AES expansion or rejection sampling
with this model remains an implementation correspondence task. Efficient
recovery of witnesses from Rust proof bytes alone is outside the theorem.
The [formal audit](../AUDIT.md) records the shared verification boundary.

## Retained models and privacy

The earlier `LfzkV2` quadratic/unpacked circuit model and its numerical
certificates remain available in their original namespaces. Their hash
geometry is different, and they are not used as a semantic replacement for
the native circuit. Shared round algebra, sparse rows, Polygero analysis,
MAC collision bounds, and generic Merkle compilers are reused.

The retained backend privacy components prove a joint response/opening
simulation and affine-MAC tag uniformity. A complete joint-view V2
zero-knowledge theorem, including native frontend transmission, packing,
commitment-dependent pads, and Merkle programming, is not claimed.

## Reproduce the checks

From `formal/`:

```sh
lake build
lake build LfzkV2.APITest
rustc --edition 2024 scripts/audit.rs -o /tmp/longfellow-source-audit
/tmp/longfellow-source-audit
lake env lean scripts/Audit.lean
```

The endpoint audit and certificates are included in the default build.
V2 proofs permit only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. The API checks cover both affine corrections, scalar and
empty proofs, malformed round counts, false assertions, and product consistency.
