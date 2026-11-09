# Formal security claims and audit

## Current MAC-free mdoc protocol

[`Current.MdocSharedSHASoundness.ratio_le`](lfzk-v2/LfzkV2/Current/MdocSharedSHASoundness.lean)
proves, for the rate-1/7 profile `(349,12,2443,84)`, that for all integers
`Q >= 0` and `Q_H >= 0`, any finite classical adaptive adversary making at most
`Q` distinct transcript-oracle queries and at most `Q_H` SHA-256-oracle calls
satisfies

```text
Pr[verifier accepts and the paired extractor fails to recover
   a witness satisfying the requested circuits]
  <= 2Q / 2^128
     + [4Q + 1 + Q_H(Q_H - 1)/2
        + (4886 + Q_H)(2Q_H + R + Q + 2)] / 2^256.
```

The experiment uses the original prover's transcript-query budget `Q` and
SHA-query budget `Q_H`; `R` is the number of ordinary round boundaries,
excluding the final seal (492/499 for two/four attributes). Query repetitions
receive the same complete answer and may be arbitrarily numerous but finite.
There is no positive-query premise. Probability is over the ideal oracles and
the adversary's private randomness.
The selected joint boundary belongs to `runtime::v2::zk`;
mdoc supplies its prime-field handoff and generated binary adapter. The canonical
source constructor uses the actual shared Merkle cut oracle and projected
committed lists. The checked binary/prime witness-list caps are
`21898356682154715916` and `451457457136012100305`. These large caps are part
of the mathematical extraction bound; no timed efficient extractor is proved.
Both fields and their complete
responses use the same column sample and one Merkle explanation.

The current proof derives the application failure cover, own-answer invariance,
whole-answer counts and disjoint role maximum. Generated adapter coefficients
are reconstructed only from strict earlier answers. The early paired extractor
is identified with backend recovery, including every frontend pad and terminal
cell. The final seal binds the complete canonical proof body. Replay queries
enter only the digest-sized Merkle remainder. No assumed bad-query cover,
local error budget or adversarial query-order premise replaces these proofs.

The event parses arbitrary serialized proof bytes, rejects malformed or trailing
bytes, and checks `RuntimeAdaptiveVerifier.verify` together with failed
extraction. The theorem derives the decoded statements, application failure
cover, local role counts, coding/list bounds and the shared Merkle explanation;
no `Execution` or supplied correspondence record is a premise. Public inputs
may be chosen adaptively; trusted circuit metadata and parser schemas remain
fixed. The first context binds binary public bits but excludes later prime
public values, which are parsed from the prime-start block. Canonical body and
query parsers, their inverses and the joint byte-oracle probability transport
are connected to the actual request replay. The requested-circuit corollary
uses the same extracted pair and derives the exact requested public vectors.
The common finite ideal answer and all sampler projections are constructed in
`IdealSamples` and `IdealRuntime`; no balanced-sampler certificate is a caller
premise. The ideal-sampler oracle model is explicit. The theorem is not machine
verification of Rust, SHAKE256 or SHA-256. Complete mdoc privacy is proved
separately by
[`MdocZeroKnowledge.statClose`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocZeroKnowledge.lean);
a timed implementation of the extractor is outside these results.
The API audit checks its endpoints for only `propext`, `Classical.choice`
and `Quot.sound`. Earlier checkpoint proof files remain unchanged.

The [consolidated assumption list](README.md#assumptions-and-remaining-correspondence-obligations)
states the ideal-sampler and trusted-implementation boundary. The conditioned
[`MdocProofRate7`](lfzk-v2/LfzkV2/Current/MdocProofRate7.lean) result is lifted
to one shared SHA function by
[`MdocSHAExperiment`](lfzk-v2/LfzkV2/Current/MdocSHAExperiment.lean) and the
endpoint above. The original serialized output, verifier decision and exact
first-context Merkle trace are preserved. The query budget refers to the
original program with its actual SHA-derived setup, and a fixed finite
auxiliary SHA marginal is averaged without an additional error term.
`Q_H` conservatively includes auxiliary SHA calls; no new transcript query
is introduced. The strict, retained conditioned endpoint remains available.

The shared finite-table transformations have one implementation in
[`SHAProbability`](lfzk-v2/LfzkV2/Current/SHAProbability.lean); soundness
does not depend on the ZK statistical-distance composition layer. One
canonical verifier construction is used for both oracle views, with domain
invariance proved for every decoded proof. The
[shared-SHA regressions](lfzk-v2/LfzkV2/Current/Tests/SharedSHA.lean) cover
interleaved auxiliary calls, repeated transcript inputs, equal digests in
different domains and an empty challenge alphabet for a phase with no
transcript calls.

### Concrete verifier components and Rust conformance

The Rust source checkpoint for the original audit is `1077bc6`. The current
hardening also checks canonical v2 field decoding, participant capacity validation
and the separation between partial constraint reduction and complete verification.
The domain supplies its arithmetic field, and commitment sessions retain their
transcript through authentication; borrowed frontend operations cannot replace it.

`Current.MdocProofRate7` specializes the generic arbitrary-proof endpoint.
`MdocAdvice` fixes the three-byte word, twenty little-endian quotient bits and
rejection of nonzero unused high bits. `ConcreteSetup` fixes degree-128 packing,
cell counts, row rounding, physical addresses and rate-1/7 evaluation nodes.
`ConcreteTopology` and `ConcreteAdapterTopology` construct frontend plans from
sparse fragments and output addresses. The concrete mdoc topology requires the
hash component to be strictly deeper than the adapter (20 versus 12 currently);
the general layered model supports other depth orders and ties.
`ConcreteMetadata` derives the prime
claim, packing source and generated adapter from the causal prefix;
`ConcreteMetadataReadback` proves successful prime decoding reconstructs that
same record. `MdocIdentifiers` constructs the field/domain identities, packing
descriptor, template identifier and individual/joint backend contexts with the
runtime's exact framing. Their final identifier hash remains an explicit
auxiliary function, as allowed by the oracle model below. The endpoint retains
only ordinary public size bounds, trusted circuit/field representations and the
adversary's query budget, without a supplied protocol-correctness certificate.

`Current.FrontendBody` decodes the actual side-specific proof arrays and rejects
missing, extra or wrong-width stages. `FrontendBodyVerifier` constructs the
frontend, affine constraints and replay together. `FrontendTranscript` matches
the writes in `runtime/v2/sumcheck/src/transcript.rs`: two round coefficients,
one terminal cross coefficient and two combine claims. Entries and explicit
assertions extend one layer answer; input entries extend the last combine
answer, as in `runtime/v2/sumcheck/src/verifier.rs` and `fragments.rs`. `ReplayBlocks` and
`FrontendPrefix` prove logical message recovery from the actual chained inputs,
including preservation under the later backend opening encoder.

`Current.ApplicationSetup.decodeChecked` constructs both frontends and their
full-cell layouts. The binary adapter is generated from the prime-field batched
claim and conversion answers; `AdapterFragment.full_product_check` derives
its equations from the generated circuit. `CellLayout` fixes private words,
packing masks, sumcheck pads and the two final fingerprint masks. Prime-field shared
inputs have no prime-field commitment address. Unused prime-field fingerprint slots
have provably zero frontend and batched coefficients. `GeneratorChecks`
derives primitive order from the exact nine runtime power checks and a checked
prime factorization, rather than accepting an order certificate.

`BackendVerifier.decodeBody_correspondence` decodes the complete binary/prime
H/Z arrays and constructs late backend correspondence on a successful prefix
decode. `OrderedOpening` retains the challenge-selected column order and salts;
it reconstructs the opening set from replay, not from serialized query indices.

`Current.RuntimeVerifier.verify` composes these components into a mathematical
runtime verifier, with `verify_true_iff` exposing its actual decoder branches
and acceptance checks. Hash and signature circuits are trusted public inputs.
The verifier does not take an `Execution`, a decoded `System`, or a semantic
acceptance checker from its caller. The adaptive runtime theorem derives its role-specific local views
and failure cover directly from these checks.

Prime-field row batching uses `BatchPacket`, which carries one actual row list and
its sampler. It does not quantify a finite-alphabet sampler over arbitrary
unbounded row lists. A concrete finite sampler instance is checked in
`Current/Tests/BatchPacket.lean`. Authentication likewise uses the runtime's
bounded serialized frontier count and exactly that many nodes; this gives a
finite proof space without padded wire data.

H/Z wire arrays are evaluations on the initial oracle nodes, not monomial
coefficients. `BackendBody` now decodes them by Lagrange interpolation; the
nontrivial-node regression in `Current/Tests/BackendBody.lean` distinguishes
the two interpretations. Batching-polynomial sample interpolation and physical
row reindexing are fixed in `BackendChallenges`: affine scalars come first,
then row-major evaluations for `u`, `m` and witness rows, with the binary field
completed before the prime field in the same answer. The sample-to-coin map
is a bijection, so it preserves uniformity without an additional error term.
Concrete byte consumption remains a codec conformance obligation; rejection
sampling need not consume a fixed number of bytes per field draw.

Canonical byte/XOF framing and concrete field arithmetic remain Rust audit
obligations. `ChainedSupport` and `RuntimeAdaptiveSupport` support distinct transcript
inputs with arbitrary repeated-call fuel. The normalization proofs preserve
the original commitment cut, Merkle oracle, acceptance and extractor; the
runtime theorem specializes these lemmas while preserving the original
query budget and commitment cut.

The runtime audit checked prime-field sumcheck, row batching, rescaling, the two
conversion challenges in one reading phase, generated binary sumcheck,
packing, joint backend batching and the shared opening. It also checked that
fragment boundaries introduce no extra query, the physical tuple rows are
`u`, `m`, witness, proximity, nonces follow the same column order, the frontier
is consumed in descending heap order without trailing nodes, and complete
verification checks the 32-byte final seal. Canonical framing, body headers,
joint context and salt encodings, public readback and complete proof parsing
are constructed in the mathematical model. The correspondence of Rust field
arithmetic, serialization and public setup/metadata computations to those
objects is checked by source audit. This is not a machine-checked Rust
semantics or compiler-correctness theorem.
The current composition also has no end-to-end honest-acceptance theorem or
complete captured Rust-to-Lean verifier replay vector. Its component round trips
and source audit validate implementation correspondence; they do not constitute
a mechanized refinement or completeness proof.

The transcript oracle idealization is explicit: each fresh canonical input
receives a uniform 32-byte link and the correctly distributed joint challenge
block, with independent auxiliary randomness. Repeated inputs receive the same
complete answer. Rust implements this using one direct SHAKE256 reader, link
feedback and rejection sampling, but a formal byte-stream coupling is outside
the accepted ideal-sampler model. The main bound has no cutoff term.

Tagged Merkle SHA-256 is modeled as a uniform 256-bit oracle restriction.
The layout-context digest is fixed public setup in the conditioned theorem. Its actual
SHA-256 computation uses the separate `polygero/joint/context/v1` domain;
conditioning on this disjoint auxiliary restriction fixes the context while
leaving Merkle answers uniform. The shared-SHA corollary constructs these
setup hashes from that same oracle and averages the auxiliary restriction.
It does not verify the concrete SHA-256 implementation.

SHA-256 also identifies the challenge-dependent generated adapter circuit.
Its `LFC3-v2-three-streams-v2` input domain is disjoint from the tagged Merkle
domains. The model treats that restriction as an independent auxiliary function
fixed by conditioning; it is not a fixed setup hash or an independent hash
function per call site. The literal domains and routing/averaging laws are
proved; Rust conformance is checked by source audit. The trusted public circuits define the application statement;
the theorem does not additionally prove high-level mdoc or hash/signature
circuit correctness.

## Retained layered checkpoint

The layered-sumcheck chain targets the immutable Rust snapshot based on
`12d5b8f`, SHA-256
`29a9b61191f73d05dbd5b9e5c08843c51d713ca39baef0eb9876eaef07847f5a`.
Its complete endpoint is
[`Layered.Joint.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Layered/Joint/RawRuntimeExtraction.lean).
The retained `Joint`, `Linear`, `Packed`, `Native`, and V1 proof files are
unchanged. New frontend-dependent replay and composition modules are separate;
scalar algebra, packing, typed backend, Merkle primitives and numerical
certificate proofs are reused.

## Layered sumcheck theorem chain

- [Entry algebra](lfzk-v2/LfzkV2/Layered/Entry.lean) remaps existing weights
  and adds independent zero-output coefficients. It permits overlapping
  coordinates, arbitrary entry depths, scalar outputs and zero-layer circuits.
  [Structural tests](lfzk-v2/LfzkV2/Layered/Tests/Structure.lean) cover those
  cases, including actual non-power-of-two contiguous offsets.
- [Quad fragments](lfzk-v2/LfzkV2/Layered/Fragments.lean) contain only sparse
  terms and index maps. [Sparse tensor semantics](lfzk-v2/LfzkV2/Layered/SparseLayer.lean)
  proves their evaluation and left/right kernels agree with the ordinary
  tensor layer. Intermediate ranges concatenate actual widths. At the shared
  input boundary ranges overlap, and coefficients add without a disjointness
  premise. Each layer retains one monomial array and one combining challenge.
- [Deterministic soundness](lfzk-v2/LfzkV2/Layered/Soundness.lean),
  [causal replay](lfzk-v2/LfzkV2/Layered/CausalReplay.lean), and
  [adaptive accounting](lfzk-v2/LfzkV2/Layered/FrontendBound.lean) cover the
  complete recursive schedule, not just the singleton mdoc case. Nonempty
  entry blocks each contribute `1/q`; assertion vectors, ordinary rounds and
  terminal challenges have their existing bounds. An empty block has no slot.
- [Actual packing rows](lfzk-v2/LfzkV2/Layered/Packed.lean) transfer to the
  final shared-input claim or the counted packing event. The
  [compiled-side constructors](lfzk-v2/LfzkV2/Layered/Runtime/CompiledFS.lean)
  prove this transfer from backend row satisfaction. They do not postulate
  the desired input equation or successful extraction. The
  [honest frontend](lfzk-v2/LfzkV2/Layered/Prover.lean),
  [honest packing bridge](lfzk-v2/LfzkV2/Layered/PackedProver.lean), and retained
  [backend construction](lfzk-v2/LfzkV2/Joint/Honest.lean) establish completeness.
- [Joint replay](lfzk-v2/LfzkV2/Layered/Joint/Causality.lean) fixes both field
  statements before backend challenges and both responses before the shared
  opening. [Authenticated extraction](lfzk-v2/LfzkV2/Layered/Joint/RawRuntimeExtraction.lean)
  yields a candidate pair satisfying both layered circuits and the retained
  MAC agreement from one explained tuple commitment.

The exact finite bound remains
`1384*(1+N)/2^128 + 19303/2^128 + 21661/2^255 +
adaptiveNumerator(5824,tA,L+(1+N))/2^256`, with `L <= 1204`.
The all-budget comparison is `(1+N+tA)/2^116`.
The [size bounds](lfzk-v2/LfzkV2/Layered/Sizes.lean) use the actual mdoc
singleton schedules: ordinary numerators at most 589 for the hash field
and 563 for the signature field, below the conservative 593 and 565 limits
used by the certificate.
The underlying geometry and candidate limits remain unchanged.

Rust correspondence still requires that the trusted schedule encodes every
output and assertion occurrence, the index maps use actual global ranges,
and padding coordinates are zero. Whole-vector ideal samples model each
output block and the complete assertion vector before the first round;
concrete transcript expansion and rejection sampling remain outside Lean.
The ordered circuits, layout and source identifiers must be bound by the
`layered-sumcheck/circuits/v1`, `enter-circuit/v1`, `assertions/v1`, and
`commitment-layout/v1` domains (the latter three share the same prefix).
The model does not parse `JPG1`, `LFV7`, or `MJP2`. Field arithmetic,
compiled-row placement, the six circuit MAC identities, balanced backend
samplers, Merkle codec/role decoders and sufficient answer-tape size remain
explicit premises. This is full composition for that mathematical model,
not verification of Rust execution or a full joint zero-knowledge theorem.

## Retained joint-commitment checkpoint

The joint-commitment V2 chain targets Rust `8943498`. Its complete endpoint
[`Joint.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Joint/RawRuntimeExtraction.lean)
proves `Pr[accept and paired extraction fails] <= (1+N+tA)/2^116` for all
adversarial transcript and Merkle query budgets. Earlier `Linear`, `Packed`,
`Native`, and V1 theorem files are preserved unchanged.

## Joint-commitment theorem chain

- [Typed families](lfzk-v2/LfzkV2/Joint/Backend.lean) use a finite ordered
  participant index, common geometry, per-field carriers and arithmetic, one
  tuple leaf, and one column query. Repeated field types remain distinct
  positions. The committed candidate family is fixed by the one extracted
  tuple; its cardinality is the product of the component list sizes.
- [Shared-query potentials](lfzk-v2/LfzkV2/Joint/Potential.lean) bound the sum
  of residual charges over the same query alphabet. They never multiply
  per-field query probabilities. [Honest construction](lfzk-v2/LfzkV2/Joint/Honest.lean)
  constructs the actual linear-only response polynomials and proves
  authenticated completeness for every shared query.
- [Replay and causality](lfzk-v2/LfzkV2/Joint/Causality.lean) put all frontend
  and packing data before either backend challenge and both responses before
  the shared opening. Both backend roles recover the same earlier statement
  message. Existing actual compiled-row transfers are reused unchanged.
- [Adaptive extraction](lfzk-v2/LfzkV2/Joint/FiatShamir.lean) combines those
  transfers and the two circuit MAC equations. The shared opening is one
  oracle slot carrying both residual charges. The returned candidate pair
  satisfies both circuits and agrees on its common message.
- [Authentication](lfzk-v2/LfzkV2/Joint/Commitment.lean) instantiates the
  generic family with the concrete ordered two-field tuple, extracts the
  whole tuple from one cut trace, and proves its resampling invariance.
  [Raw replay](lfzk-v2/LfzkV2/Joint/RawExtraction.lean) derives the MAC answer
  with one verifier lookup; no supplied-answer coherence hypothesis remains.

The exact finite bound is

```text
1384*(1+N)/2^128 + 19303/2^128 + 21661/2^255
  + adaptiveNumerator(5824,tA,L+(1+N))/2^256,  L <= 1204.
```

The merged opening raises the local coefficient from 925 to `925+459=1384`;
the total verifier charge is unchanged. One Merkle explanation replaces two,
with `2*2912=5824` checking queries. The checked all-budget 116-bit comparison
uses the same small-Merkle argument and does not assume independence.

Explicit premises identify the two actual compiled sides and their certified
profiles, the shared query sampler, balanced ideal samplers, native circuits
and input layouts, MAC row identities, field sizes, the Merkle codec/decoders,
and sufficient answer tape `TM >= 5824+tA`. Context and transcript encodings
must bind the ordered field/domain/layout identities and all source digests
and counts, as in the target runtime. These are implementation correspondence
obligations; Rust execution and concrete cryptographic primitives are not
verified by Lean. The `JPG1`/`LFV6`/`MJP1` bytes are not parsed by this model.
No full joint zero-knowledge theorem is asserted.

## Retained linear-terminal checkpoint

The linear-terminal V2 soundness chain reaches the modeled authenticated
verifier at commit `21cb029`, including native affine circuits, binary-input
packing, the linear-only Polygero backend, raw proofs, and the
verifier-recomputed MAC key. Its checked all-budget result is

```text
Pr[both sides accept and paired extraction fails] <= (1 + N + tA) / 2^116.
```

`N` counts adversarial Fiat–Shamir queries and `tA` counts adversarial
Merkle-hash queries. The finite experiment permits recommitment, arbitrary
query order, and adaptive proof selection. The earlier `fcf8a3a`
product-checked checkpoint retains its separate 117-bit theorem unchanged.

## Linear-terminal theorem chain

[`LinearTerminal`](sumcheck-v2/SumcheckV2/LinearTerminal.lean) proves that a
false terminal claim can pass at at most two nonzero scales. The committed
product pad is arbitrary in soundness. The polynomial's constant term is the
false claim, its linear coefficient includes the cross message sent before
the scale, and its quadratic coefficient is `pAB-pA*pB`. No product-consistency
premise survives in the verifier, compiler transfer, or extraction proof.
[`Linear.CausalReplay`](lfzk-v2/LfzkV2/Linear/CausalReplay.lean) fixes this
polynomial before the scale and the recovered pair before the combining
challenge. The ideal nonzero sampler has exactly `|F|-1` possible outputs.

[`Linear.Runtime.CompiledFS`](lfzk-v2/LfzkV2/Linear/Runtime/CompiledFS.lean)
constructs the direct and packed affine row systems and proves their transfer
from actual backend satisfaction. Its side instances require `nq=0`; shared
Polygero theorems then have an empty product predicate. All witness and mask
rows are ordinary opened rows. Packing, MAC, and Merkle lemmas are reused.
[`ProfiledSide`](lfzk-v2/LfzkV2/Linear/Runtime/ProfiledSide.lean) supplies the
same certified geometries and candidate lists as the retained checkpoint.

[`RawExtraction.probability_le`](lfzk-v2/LfzkV2/Linear/Runtime/RawExtraction.lean)
includes both authenticated opening checks, common cut-trace extraction,
adaptive transcript accounting, and verifier replay of the MAC lookup.
[`RawRuntimeExtraction.probability_bound`](lfzk-v2/LfzkV2/Linear/Runtime/RawRuntimeExtraction.lean)
proves the conservative bound

```text
925*(1+N)/2^128 + 19303/2^128 + 21661/2^255
  + 2*adaptiveNumerator(11648,tA,L+(1+N))/2^256,  L <= 1205.
```

The exact normalized frontend term is
`B*(N*max(max(out,2)/q,2/(q-1)) + (out+sharpLayerBudget)/q + 2*layers/(q-1))`.
The numerical certificate uses 20 hash layers and 21 signature layers and
conservatively bounds `2/(q-1)` by `4/q`; it is not an optimal-security claim.
The previous 117-bit unit-offset certificate is not asserted for this model.
`extraction_116` combines the new cost with the existing small-Merkle argument
for every pair of query budgets. No additional distinct-leaf premise is used.

[`LinearTerminalMasking`](sumcheck-v2/SumcheckV2/LinearTerminalMasking.lean)
proves an invertible honest map between three independent pads and the cross
message/two masked claims when the scale is nonzero. This local fact does not
establish full joint zero knowledge. Rust byte encodings, concrete rejection
sampling, and arithmetic remain correspondence obligations.

## Checked endpoints

| Claim | Theorem or build target | Scope |
|---|---|---|
| Current mdoc V2 extraction with one SHA oracle | [`MdocSharedSHASoundness.ratio_le`](lfzk-v2/LfzkV2/Current/MdocSharedSHASoundness.lean) | `2Q/2^128` plus the explicit squared-field remainder; original query budget, adaptive requests, canonical proof bytes and exact first-context extraction. |
| Joint-commitment V2 authenticated extraction, all budgets | [`Joint.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Joint/RawRuntimeExtraction.lean) | `(1+N+tA)/2^116`, for `8943498`; one tree, shared queries, exact finite bound. |
| Linear-terminal V2 authenticated extraction, all budgets | [`Linear.Runtime.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Linear/Runtime/RawRuntimeExtraction.lean) | `(1+N+tA)/2^116`, for snapshot `21cb029`; exact finite bound also proved. |
| Retained product-checked V2 extraction, all budgets | [`Packed.RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/Packed/RawRuntimeExtraction.lean) | `(1+N+tA)/2^117`, under the model premises below. |
| Packed V2 actual compiler instances | [`Packed.Compiled.side`, `Packed.Direct.side`](lfzk-v2/LfzkV2/Packed/CompiledFS.lean), [`ProfiledSide`](lfzk-v2/LfzkV2/Packed/ProfiledSide.lean) | Actual row construction proves the frontend transfer; the profile chooses its candidate bound before that transfer and counting proof. |
| Earlier unpacked V2 authenticated composition | [`RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/RawRuntimeExtraction.lean) | Retained separate model, with earlier hash geometry and frontend budgets. Its numbered-leaf and annotated-proof variants are not needed by the packed endpoint. |
| Retained standalone Polygero profiles | [`Profile.fs_extraction_failure_127`](parameters/polygero/PolygeroRustHahn.lean) | `(N+1)/2^127`, including satisfiable transcript-dependent statements, in the ideal-binding, uniform-sampler model. Frontend, packing, MAC, and Merkle costs are excluded from this component result. |
| V1 combined extraction and false-statement soundness, all four v7 hash profiles | [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) | `(1+N+tA)/2^116`, under V1's documented circuit, sampler, transcript, and MAC-key coherence premises. |
| Current mdoc statistical zero knowledge | [`MdocZeroKnowledge.statClose`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocZeroKnowledge.lean) | Complete witness-free simulation, arbitrary private observer state and raw traces, one shared SHA oracle; explicit rate-1/7 error and ideal-sampler/trusted-application premises. |
| Fiat–Shamir backend coupling foundations | [`PolygeroZk.adaptive_translate`](lfzk-v2/LfzkV2/PolygeroZk.lean), [`Backend.coupling_view`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/Backend.lean) | Algebraic changes of private coins used by the complete mdoc Fiat–Shamir privacy theorem. |
| Dual-packing adapter | [`Instance.linear_native_soundness_probability`](dual-packing/DualPacking/ArtinSchreierBackend.lean) | At most `1/|F|` for a false fixed claim, with arbitrary committed cells and an independent uniform vector challenge. `LfzkV2.Packed` composes it with the native frontend, backend and Fiat–Shamir analysis. |

## Retained product-checked theorem chain

1. [`Packed.RawExtraction.key_coherent`](lfzk-v2/LfzkV2/Packed/RawExtraction.lean)
   derives the MAC answer from the verifier lookup. `probability` has no
   supplied-key coherence conjunct. `probability_eq_annotated` proves that
   its raw acceptance/failure event equals the annotated experiment.
2. [`Packed.TwoFieldCommitmentFS.extraction_le`](lfzk-v2/LfzkV2/Packed/TwoFieldCommitmentFS.lean)
   reduces both authenticated opening checks to one shared cut-trace
   context, adding both Merkle explanation errors. The committed oracles'
   resampling invariants are proved rather than assumed.
3. [`Packed.TwoFieldFS.extraction_le`](lfzk-v2/LfzkV2/Packed/TwoFieldFS.lean) applies the
   adaptive potential compiler to the merged MAC/hash/signature schedule.
   Each adversarial query pays the maximum local budget across roles.
4. [`Packed.TwoFieldPotential.extract_valid`](lfzk-v2/LfzkV2/Packed/TwoFieldPotential.lean)
   proves that a returned pair satisfies both circuits and agrees on its
   common message. The V2 MAC is `av*message+ap`; the two private additive
   pads may differ. A fixed pair of unequal messages collides at at most
   one multiplier. V1's shifted multiplicative tag is not used as the V2
   MAC definition.
5. [`Native.CausalReplay`](lfzk-v2/LfzkV2/Native/CausalReplay.lean) and
   [`Native.HashReplay`](lfzk-v2/LfzkV2/Native/HashReplay.lean) prove that the
   affine frontend's bad-event tests depend only on their challenge prefixes.
   [`Packed.Replay`](lfzk-v2/LfzkV2/Packed/Replay.lean) places the vector
   packing challenge after `U` and before `A` and the backend challenges.
   [`Packed.FiatShamir.event_soundness_le`](lfzk-v2/LfzkV2/Packed/FiatShamir.lean)
   charges this stage only on the packed side; the direct side has no packing
   role or budget.
6. [`Packed.Backend`](lfzk-v2/LfzkV2/Packed/Backend.lean) proves that the
   actual authenticated rows and product checks read the same committed
   cells. [`Packed.Inputs`](lfzk-v2/LfzkV2/Packed/Inputs.lean) connects the
   final source claim to public inputs and canonical private coordinates;
   unused tail coordinates receive zero coefficients. Binary coordinates
   are bits even for adversarial committed words.
   [`Packed.Counting`](lfzk-v2/LfzkV2/Packed/Counting.lean) eliminates the
   later scalar response from the bad event and proves a candidate-list
   bound of `L/|F|`. [`Packed.CompiledFS`](lfzk-v2/LfzkV2/Packed/CompiledFS.lean)
   constructs both actual row systems and proves their transfer to the native
   frontend. No desired extraction conclusion is assumed at that boundary.
7. [`Packed.ProfiledSide`](lfzk-v2/LfzkV2/Packed/ProfiledSide.lean),
   [`Packed.RuntimeProfiles`](lfzk-v2/LfzkV2/Packed/RuntimeProfiles.lean),
   [`Packed.RuntimeCost`](lfzk-v2/LfzkV2/Packed/RuntimeCost.lean), and
   [`Packed.RuntimeSecurity`](lfzk-v2/LfzkV2/Packed/RuntimeSecurity.lean)
   discharge the candidate, tail, and rational numerical comparisons.
   The annotated cost is
   `925*N/2^128 + 17303/2^128 + 18889/2^255`, before the two Merkle terms.
   Raw replay adds one verifier lookup to this count. For `tA ≥ 8`,
   `tsec_117_of_merkle_ge` absorbs that lookup and the startup cost into
   `(1+N+tA)/2^117`. For `tA < 8`,
   [`SmallMerkle`](bcs/Bcs/SmallMerkle.lean) bounds authenticated acceptance
   itself by `(2*tA^2+(11648+tA)*(2*tA+1))/2^256`, at most
   `174923/2^256`. At fixed transcript oracle, the complete prover is a
   bounded Merkle program; averaging restores arbitrary transcript
   queries without an `N` factor. One authentication path requires at
   least eight distinct queries unless a predictable child digest is hit.
   This proves the final endpoint without any additional numbering or
   leaf/node separation premise.

The earlier unpacked theorem chain remains in the unprefixed `LfzkV2`
modules. Its hash geometry is `(3584,512,18,87)`, its sharp frontend budgets
are 655 and 552, and its annotated cost is
`737*N/2^128 + 16383/2^128 + 18460/2^255`. Those constants and its stronger
87-numbered-leaf intermediate bound do not describe the packed checkpoint.

The extractor is a mathematical search in the two lists associated with
the committed oracles. The theorem bounds acceptance without a matching
satisfying pair; it does not claim that decoding the Rust proof bytes alone
efficiently recovers a witness.

## Premises and implementation boundary

Both packed numerical endpoints retain the following explicit premises;
the linear-terminal endpoint additionally bounds hash/signature layers by
20/21 and samples each terminal scale uniformly from the nonzero field:

- Hash and signature geometries `(n,k,s,t) = (2912,416,15,86)`, with the
  instance's distinct evaluation points and decoder/column encodings.
  The analysis uses hash cutoff 1136 and candidate bound 25; the signature
  cutoff is 1127 with candidate bound 33. The concrete profile constructors
  discharge these bindings and the terminal-budget equalities.
- Hash and MAC fields of size at least `2^128`, signature field size at
  least `2^255`, and Merkle digest alphabet of size exactly `2^256`.
- Balanced finite samplers for every frontend block, packing vector, backend coin,
  opening-query role, and the MAC multiplier, on one common transcript
  answer alphabet. These are ideal sampler assumptions, not a claim that
  every challenge tuple is one 256-bit digest.
- Trusted circuit layouts, the packing basis and cell maps, and public/private
  input embeddings. Output dimensions are at most 5 and 3; the combined
  output-plus-sharp-layer frontend budgets are at most 593 and 565.
  For every satisfying committed candidate, the two circuit MAC
  rows agree with the shared public tag. These correspondence premises
  are not consequences of a backend numerical certificate.
- The declared Merkle codec and role decoders, and enough finite answer
  tape for the bounded execution: `TM ≥ tA + 11648`.

The retained checkpoint used `polygero/root/original-leaf/v1` for leaves
and `polygero/root/node/v1` for internal nodes. The current runtime's
[`merkle/src/hash.rs`](../rust/runtime/v2/merkle/src/hash.rs) uses
`polygero/joint/leaf/v1` and `polygero/joint/node/v1`; these are also the
[current model's domains](lfzk-v2/LfzkV2/Current/MerkleWireCodec.lean).
Both layouts include the context, column index as a little-endian `u64`,
salt and canonical column bytes in each leaf.
[`verifier.rs`](../rust/runtime/v2/polygero/src/verifier.rs) hashes each opened
column with its sampled index before verifying the Merkle paths;
[`transcript.rs`](../rust/runtime/v2/polygero/src/transcript.rs) samples
distinct indices. Thus repeated column values do not identify leaf
preimages at different positions. `OpeningClaim.DistinctLeafInputs` is the
explicit codec correspondence premise for the stronger 87-query lemma;
`distinctLeafInputs_of_index` derives it from an index decoder. The packed
all-budget theorem uses the weaker path-depth argument and does not need
this extra correspondence premise. Neither argument assumes 87 independent
digest guesses: the bound retains the predictable-target counting factor.

This is end-to-end soundness for the stated mathematical verifier model.
It is not source-level verification of Rust or C++. Limb arithmetic,
overflow, allocation bounds, parser validation, serialization, domain/hash
encodings, and the concrete SHA/AES expansion and rejection samplers remain
implementation correspondence obligations. The replay model preserves the
protocol's challenge order and prefixes; byte-level transcript equivalence
is outside the theorem. The individual registered application's circuit
semantics must also be related to the modeled trusted circuit.

The retained `LfzkV2.Packed` checkpoint describes `fcf8a3a`; the separate
`LfzkV2.Linear.Runtime` theorem chain describes `21cb029`. Later runtime
changes require their own correspondence and cost audit.

The current MAC-free mdoc privacy theorem combines causal frontend
transmission, commitment-dependent pads, cross-field conversion, packing,
the joint backend, Merkle hiding, and transcript programming. For any event
in the complete real or simulated observer view, its probability difference
is at most
`(47745992+4886*Mpre+4718*Mpost)/2^320 + 47716680/2^256 + 4884*Mpre/2^512 + Tpre/2^46208`.
The private observer context and both original raw traces are retained.
The witness map is fixed per public request, and valid only at actual reachable
requests. Trusted ordinary hash assertions must be independent of the reserved
mask/OTP suffix and generated adapter parameters; signature correctness is
also trusted. Public representation bounds and generator/basis checks remain
explicit. Private randomness is uniform, and the ideal whole-answer transcript
sampler is the approved abstraction: full rejected SHAKE streams and machine
execution are not proved. The [precise theorem scope](lfzk-v2/README.md#complete-mdoc-zero-knowledge)
and axiom tests document this boundary.

## Reproduce the audit

From `formal/`, after installing the pinned Lean toolchain and Mathlib:

```sh
lake build
rustc --edition 2024 scripts/audit.rs -o /tmp/longfellow-source-audit
/tmp/longfellow-source-audit
lake env lean scripts/Audit.lean
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-profile
cargo run --release --manifest-path lfzk-v1/scripts/Cargo.toml --bin inspect-v7-assertions
```

The default build includes all retained Hahn certificate families, both
sumcheck libraries, dual packing, the four V1 116-bit endpoints, the V2 endpoint audit,
and the Polygero API/dependency checks. `scripts/build.sh` uses Lake's default
concurrency. There is no separate certificate build requirement.

The Rust source scanner strips nested Lean comments and strings before
rejecting unchecked proof constructs. It also validates local Markdown
links in the formal and Rust documentation. The Lean audit inspects every
imported declaration owned by the V1/V2, sumcheck, dual-packing, witness-selection,
chained-transcript, BCS, Merkle, Polygero,
runtime-Hahn, and runtime-profile modules, including private helpers.
V2 and the other audited non-V1 modules permit only `propext`,
`Classical.choice`, and `Quot.sound`. V1 numerical rows retain the documented
native-evaluation allowance, including their imported legacy numerical
certificates. V2 and the retained Hahn identities do not depend on that
allowance.

The broad audit is separate from the default build so repeated incremental
builds keep their short API and certificate checks. These checks establish
the stated proof dependencies and exact numerical facts; they do not
discharge the implementation correspondence premises above.

The default build checks both the retained checkpoint and the linear-terminal
API. The latter includes arbitrary malicious product pads, two distinct bad
terminal scales, characteristic-two completeness, and nonzero-scale masking.
The full dependency and source/link audits also include the new V2 modules.

The V1 Rust inspectors load the frozen archives through the current
single-crate runtime, recompute archive and circuit IDs, compare the five
recorded circuit/geometry profiles, and reject violations of the structural
assertion premises. The older Python launchers targeting the former crate
layout have been removed. The remaining legacy numerical reporting scripts
do not participate in the trusted Lean proof chain.
