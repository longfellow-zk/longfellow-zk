# Longfellow V2: extraction and soundness

## Current MAC-free protocol

[`MdocSharedSHASoundness.ratio_le`](LfzkV2/Current/MdocSharedSHASoundness.lean) proves
Fiat–Shamir extractor soundness for the modeled runtime verifier with adaptive
public requests, arbitrary serialized proof bytes, and the explicit ideal
sampler oracle. For every pair of integers `Q >= 0` and `Q_H >= 0`, any finite
classical adaptive adversary making at most `Q` distinct transcript-oracle
queries and at most `Q_H` SHA-256-oracle calls satisfies

```text
Pr[verifier accepts and the paired extractor fails to recover
   a witness satisfying the requested circuits]
  <= 2Q / 2^128
     + [4Q + 1 + Q_H(Q_H - 1)/2
        + (4886 + Q_H)(2Q_H + R + Q + 2)] / 2^256.
```

`R` counts ordinary round boundaries, excluding the final seal: 492 for two
attributes and 499 for four. The bound includes `Q = 0` and arbitrary finite
query repetitions, which return the same complete answer. There is no
minimum-query premise. Probability is over the ideal oracles and the
adversary's private randomness; the uniform bound for each fixed private
choice also bounds their average. Verifier replay appears only in the
squared-field remainder. For `q=2^128` the leading per-query charge is
`2/q = 2^-127`; positive squared-field corrections remain explicit.

The ordinary rate-1/7 profile is `(k,s,n,t)=(349,12,2443,84)`. Its
[exact Hahn certificate](LfzkV2/Current/Parameters/Rate7.lean) and list bounds
are checked internally. The theorem derives verifier acceptance, application
failure coverage, query charging, the role maximum, and one shared Merkle
explanation. No `Execution`, semantic correspondence record, bad-event cover,
sampler law or coding-error budget is a caller-supplied certificate.

The mdoc specialization fixes the canonical three-byte quotient-advice parser,
degree-128 binary packing, committed-cell layout, rate-1/7 backend geometry,
evaluation-node order and scalar challenge readers. Sparse circuit topology
constructs both the algebraic verifier and its transcript plan. Derived prime
claims, generated adapter identifiers and backend contexts are computed from
the actual earlier messages and answers. Packing writes its caller-supplied
statement and public cell counts, not the derived coefficients or affine RHS.
The source is reconstructed from earlier bound messages and answers on the
same oracle history; the statement bytes alone need not determine it.
[`readPackingPacket_off`](LfzkV2/Current/ApplicationViews.lean) proves that
varying the current packing answer cannot change this source. Accepted-path
readback identifies it with the frontend's actual input claim. U is still
bound before the packing query, and A before joint backend challenges. The generic
[`IdealProofRate7`](LfzkV2/Current/IdealProofRate7.lean) theorem remains available
for other trusted setups; the mdoc endpoint takes no independent advice decoder,
metadata callback, transcript plan or backend-layout certificate.
The concrete mdoc topology supports a hash component strictly deeper than its
adapter; this ordinary depth restriction is explicit in its setup bounds.
The current hash and adapter have respectively 20 and 12 layers. The general
layered-sumcheck model still supports components in either depth order and ties.

### Oracle and implementation boundary

A fresh transcript-oracle input supplies one uniform 32-byte link and the
correctly distributed joint challenge block. Independent auxiliary randomness
may also be exposed to the prover. The common finite answer alphabet and all
sampler projections are constructed in
[`IdealSamples`](LfzkV2/Current/IdealSamples.lean) and
[`IdealRuntime`](LfzkV2/Current/IdealRuntime.lean): full-field vectors, nonzero
terminal/conversion scalars, both fields' fingerprints, joint backend samples,
and ordered openings. The same input always returns the same answer.

This is the **ideal-sampler oracle assumption**. Rust's direct SHAKE256 reader
and rejection sampling are audited against it; a formal coupling to complete
SHAKE output byte streams is outside the theorem. There is no runtime retry
limit or extra sampling round.

The tagged Merkle SHA-256 restriction is an independent 256-bit random oracle.
Non-Merkle SHA-256 domains, including setup identifiers and the generated
adapter's circuit identifier, are disjoint auxiliary restrictions of the same
ideal SHA-256 function. Conditioning on that auxiliary function fixes the
public setup and causal identifier computations while leaving Merkle answers
uniform. The conditioned theorem
[`MdocProofRate7.ratio_le`](LfzkV2/Current/MdocProofRate7.lean)
quantifies those fixed public values. The shared-SHA endpoint applies it at
every complementary restriction, then averages an arbitrary independent
finite auxiliary marginal. A common transcript window covers all public
setup values and every possible program branch before sampling.
[`MdocSHAExperiment`](LfzkV2/Current/MdocSHAExperiment.lean) proves setup and
causal metadata equality, preservation of the original serialized output,
the exact first-context Merkle prefix, and verifier/extraction-event equality.
The original program's distinct transcript-query budget is preserved.
`Q_H` conservatively counts all of its SHA calls, including auxiliary inputs;
there is no extra domain-splitting error. Neither theorem proves SHA-256 or
SHAKE cryptographic security.

The [shared finite-table algebra](LfzkV2/Current/SHAProbability.lean) owns
oracle-coordinate splitting, window inclusion and finite extension. The ZK
statistical-distance lifts and soundness counting bounds use the same maps.
[`SHALazy`](LfzkV2/Current/SHALazy.lean) identifies lazy and functional
executions directly, without an artificial default transcript challenge.
[`MdocSHAExperiment.verify_merge`](LfzkV2/Current/MdocSHAExperiment.lean)
uses one canonical verifier construction and proves its domain invariance
for arbitrary decoded proofs and Merkle functions.

Hash/signature circuits, their public topology, field arithmetic and canonical
scalar representations are trusted mathematical setup. The original Rust
source audit used checkpoint `1077bc6`; the current hardening also checks
canonical v2 field decoding, participant capacity validation, domain-owned field
selection and transcript ownership through commitment authentication. This remains
a source audit, rather than a machine-checked Rust semantics/compiler proof.
The theorem retains ordinary public geometry, capacity, address and length
checks; these are not assumed soundness conclusions. See the
[implementation audit](../AUDIT.md) and the consolidated
[assumptions and remaining obligations](../README.md#assumptions-and-remaining-correspondence-obligations).
The normal Rust mdoc loader trusts the actual archive payloads and skips
semantic payload-ID recomputation; advertised identifiers alone do not
establish that correspondence.

### Runtime and transcript

The selected joint boundary belongs to `runtime::v2::zk`, in `runtime/v2/zk`.
Witness selection and Polygero are sibling protocols underneath it. Mdoc
provides the prime-field handoff and the generated binary adapter.

| Boundary | Data bound before the challenge | Answer block |
|---|---|---|
| Witness selection | Joint root, field identities and layouts | Two independent full coefficient vectors per field |
| Prime layered sumcheck | Public prime inputs and preceding masked messages | Shared assertion/entry coefficients, ordinary rounds, nonzero terminals and combine coefficients |
| Prime row batching | All compiled rows and final input equation | One independent weight per row |
| Rescaling | Complete derived prime linear claim | One nonzero prime scalar |
| Conversion | Scaled shared coefficients and masked opening `mu` | Two nonzero prime scalars in one answer |
| Binary layered sumcheck | Masked quotient advice and public statements | One shared sumcheck over all quad fragments |
| Packing | Source claim and trace-zero vector `U` | One full-field vector; absent for degree one |
| Joint Polygero batching | Both completed frontend prefixes and packing response `A` | Both fields' affine weights and polynomial samples |
| Shared opening | Both complete `H/Z` response pairs | One ordered sample of 84 distinct columns |
| Final seal | Chained prefix and complete canonical proof body | Separately domain-separated 32-byte seal |

Each field commits two dedicated fingerprint masks before coefficient sampling.
They are backend auxiliary cells, excluded from the original-cell coefficient
vectors. All four masked responses are bound before either sumcheck. The prime
commitment excludes the shared bit prefix: its inputs are reconstructed from
the selected binary witness. Binary public bits are bound at the first boundary;
prime public inputs are bound when the prime frontend starts. No future prime
values are added to the earlier fingerprint key.

One `begin_squeeze()` supplies one boundary answer, including every challenge
read without an intervening prover message. Fragments add no boundaries or wire
arrays. Components are ordered by decreasing depth, with original input index
breaking ties, including duplicate circuit identifiers. Outputs are zero
assertions at their own layer; entering outputs and explicit assertions share
one answer. Input-only assertions extend the final combine answer.

A frontend with layers has `sum(logw)+3*depth` boundaries. A frontend without
layers has one input-assertion boundary. Besides both frontends there are six
ordinary boundaries, one optional packing boundary, and the final seal. The
measured two-/four-attribute presentations have respectively 492/499 ordinary
boundaries, followed by one final-seal query. Binding source circuit identifiers
adds no separate query. Current sizes and timings are in the
[Rust README](../../rust/README.md#performance).

### Checked encoding and acceptance

[`ProofBodyCodec`](LfzkV2/Current/ProofBodyCodec.lean) models the canonical
MDA6/JPG2 body, including the terminal authentication frontier.
[`ProofOutput`](LfzkV2/Current/ProofOutput.lean) parses that body and its seal;
malformed or trailing proof bytes are rejected inside the final event, without
a parser-success premise. `H/Z` wire values are oracle-prefix evaluations and
are interpolated by the backend decoder. The shared leaf order is binary then
prime, each with physical rows `u`, `m`, witness rows and `fstar`; nonces follow
the sampled-column order.

[`QueryRuntime`](LfzkV2/Current/QueryRuntime.lean) reconstructs contexts and
fresh-message caches from actual query bytes. Inconsistent logical aliases lie
outside its canonical image.
[`CanonicalVerifierAgreement`](LfzkV2/Current/CanonicalVerifierAgreement.lean)
proves complete replay, decoding and verification depend only on that image.
[`CanonicalOracle`](LfzkV2/Current/CanonicalOracle.lean) preserves the original
first-context Merkle extractor when transporting the oracle program.
[`MerkleWireCodec`](LfzkV2/Current/MerkleWireCodec.lean) constructs exact leaf/node
preimages and their role decoders; injectivity is proved from their parsers.

[`CanonicalRuntime.decoded_true_at_request`](LfzkV2/Current/CanonicalRuntime.lean)
derives both circuit satisfactions at the actual requested public vectors from
the same extracted pair. The binary conclusion covers the generated
hash/adapter circuit; its adapter product semantics are proved. The prime
conclusion covers the trusted signature circuit, with shared bits taken from
the binary witness.

The extractor is a mathematical finite search. No efficient enumeration bound
is claimed for the worst-case binary/prime candidate caps
`21898356682154715916` and `451457457136012100305`. The theorem establishes
extractor soundness; the separate complete privacy theorem follows below.

The default build checks the current tests and endpoint axioms, allowing only
`propext`, `Classical.choice` and `Quot.sound`. Retained checkpoint and V1 proofs
remain in their original namespaces.

### Complete mdoc zero knowledge

[`MdocZeroKnowledge.statClose`](LfzkV2/Current/ZeroKnowledge/MdocZeroKnowledge.lean)
proves statistical zero knowledge for the complete rate-1/7 mdoc runtime model.
For every bounded classical observer and every distinguishing event `E`,

```text
|Pr[real view ∈ E] - Pr[simulated view ∈ E]|
  <= (95462672 + 4886*Mpre + 4718*Mpost)/2^256
     + 4884*Mpre/2^512 + Tpre/2^46208.
```

`Mpre` and `Mpost` bound the observer's SHA queries before and after the
proof; `Tpre` bounds earlier transcript queries. All budgets may be zero.
The observer may retain arbitrary private state and make arbitrary malformed
or repeated raw input queries. Its complete proof, private state, final output,
and both ordered raw query/answer traces form the compared view. Later
transcript queries have any finite bound and add no separate error term.

The explicit `MdocZeroKnowledge.simulate` has no witness argument. It calls
the public frontend/backend simulator, constructs ordered authentication data,
and computes the final seal normally. The real and simulated experiments use
the same SHA function for public setup, causal identifiers, Merkle hashing,
and observer queries. The theorem samples one fixed finite SHA marginal,
including any additional coordinates, and one fixed raw transcript marginal;
it does not condition independence on an observed adaptive trace. Finite
private-state support is derived internally from the observer's bounded
program. No execution, layout, coverage or simulator certificate is a premise.

The theorem holds for every fixed witness map per public request, with
validity needed only for actually reachable requests. The trusted application
premises are signature-circuit satisfaction and `MdocWitness.HashValid`:
ordinary non-adapter hash assertions hold for the fixed document prefix
uniformly over the reserved mask/OTP suffix and generated adapter parameters.
Generated adapter equations and runtime/backend row satisfaction are proved.
Ordinary public shape/serialization bounds, basis coordinate zero equal to one,
and the executed primitive-generator check remain explicit setup conditions.

Private coins are independent and uniform. SHA-256 is idealized as a random
oracle with its literal domain tags. The transcript oracle supplies a whole
link/challenge answer with ideal uniform rejection sampling, as described
above. Raw input strings are modeled; a coupling to rejected SHAKE bytes or
unused XOF output is outside this theorem. This is a theorem about the Lean
runtime model, rather than machine verification of Rust or a formal running-time
bound for the simulator. Its axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`.

## Retained layered checkpoint

The `LfzkV2.Layered` namespace models layered sumcheck with sparse quad
fragments, one dense wire array per layer, and one shared input array. Its
[authenticated extraction endpoint](LfzkV2/Layered/Joint/RawRuntimeExtraction.lean)
proves `Pr[accept and paired extraction fails] <= (1+N+tA)/2^116` for every
transcript-query budget `N` and Merkle-query budget `tA`.

The source checkpoint is the immutable Rust snapshot based on `12d5b8f`,
SHA-256 `29a9b61191f73d05dbd5b9e5c08843c51d713ca39baef0eb9876eaef07847f5a`.
It uses `JPG1`, `LFV7`, and `MJP2`. The bound covers the new layered frontend,
its final packing reduction, both field checks, the retained affine MAC,
and one authenticated tuple commitment with shared column queries.

[Entries](LfzkV2/Layered/Entry.lean) add independently weighted zero outputs
at any layer boundary, including scalar outputs and zero-layer circuits.
Each nonempty entry block costs at most `1/q`; the proof does not assume
that only one circuit is present. [Sparse layers](LfzkV2/Layered/SparseLayer.lean)
translate local term indices into global coordinates and prove that fragment
traversal evaluates the same tensors. Input ranges may overlap: their
contributions add. Intermediate arrays concatenate actual widths; only the
tail of the global array has implicit zero padding. There are no component
index rounds, separate component terminal factors, or extra advice rows.

The [soundness reduction](LfzkV2/Layered/Soundness.lean) and
[causal replay](LfzkV2/Layered/CausalReplay.lean) cover arbitrary finite depth
schedules. Each ordinary layer has one sumcheck, one randomized linear
terminal check, and one combining challenge. Assertion coefficients are
independent of output weights. The [packing bridge](LfzkV2/Layered/Packed.lean)
proves the actual compiled rows authenticate the final shared-input claim;
it never assumes arbitrary committed extension-field cells are bits.
[Honest frontend construction](LfzkV2/Layered/Prover.lean) and
[honest packing rows](LfzkV2/Layered/PackedProver.lean) compose with the retained
[typed backend completeness theorem](LfzkV2/Joint/Honest.lean).

For a circuit schedule, let `B` be the number of nonempty output-entry
blocks, `R` the sum of global layer round counts, and `D` its depth. Its
ordinary challenge numerator is at most `B + 2R + 2D`, divided by `q`; nonzero terminal scales
add `2D/(q-1)`. The [adaptive frontend theorem](LfzkV2/Layered/FrontendBound.lean)
counts every entry, assertion, round, terminal, and combining event. The mdoc
fields remain singleton schedules: the ordinary numerators are at most 589
and 563. The complete certificate conservatively retains the previous
593 and 565 limits and hence the same exact finite bound:

```text
1384*(1+N)/2^128 + 19303/2^128 + 21661/2^255
  + adaptiveNumerator(5824,tA,L+(1+N))/2^256,  L <= 1204.
```

The geometry remains `(k,s,n,t)=(416,15,2912,86)`, with candidate limits 25
and 33. The theorem's explicit premises cover correspondence of the trusted
circuit schedule and layouts to Rust, balanced ideal challenge samplers,
field sizes, compiler row placement, MAC identities and Merkle encoding.
Concrete byte parsing, hash expansion/rejection sampling and Rust execution
are not verified by Lean. Full joint zero knowledge is not claimed.

## Retained joint-commitment checkpoint

The `LfzkV2.Joint` namespace models Rust commit `8943498`: one typed Polygero
column tree and one shared opening set for the hash and signature fields.
[`Joint.RawRuntimeExtraction.extraction_116`](LfzkV2/Joint/RawRuntimeExtraction.lean)
proves complete authenticated raw-proof extraction with the packed/direct
frontends, randomized linear terminal, and retained affine MAC.

The generic [family](LfzkV2/Joint/Backend.lean) accepts any nonempty ordered
list of typed participants, including singletons and repeated field types.
Each field retains its own arithmetic, masks and challenge coins. One
explained tuple opening transfers all field checks to one fixed committed
family. The [honest construction](LfzkV2/Joint/Honest.lean) proves that the
actual response polynomials and a salted Merkle opening verify for every
shared query set. It needs ordinary statement satisfaction, not a verifier
acceptance hypothesis.

The [causal replay](LfzkV2/Joint/Causality.lean) puts both frontends and their
packing data before either backend challenge. Both statements are fixed at
the first backend point; later roles recover that same statement data. Both
field responses precede the single opening challenge. The shared-query
residual charge is a sum, not a product: correlated failures contribute
`925/2^128 + 459/2^128`. No field-independence assumption is used.

The exact raw-proof bound is

```text
1384*(1+N)/2^128 + 19303/2^128 + 21661/2^255
  + adaptiveNumerator(5824,tA,L+(1+N))/2^256,  L <= 1204.
```

The all-budget certificate remains `(1+N+tA)/2^116`. It is a conservative
bound, not an optimal-security claim. The geometry is still
`(k,s,n,t)=(416,15,2912,86)` with candidate limits 25 and 33. The model targets
this immutable commit; later sumcheck or MAC changes are outside its scope.
The byte markers are `JPG1`, `LFV6`, and `MJP1`. Encoding, field arithmetic,
concrete hash expansion/rejection sampling, and the six circuit MAC values
remain explicit implementation correspondence obligations. Complete joint
zero knowledge is not claimed.

## Retained linear-terminal checkpoint

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
simulation and affine-MAC tag uniformity for their older models. The complete
mdoc privacy theorem above concerns the current MAC-free protocol.

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
