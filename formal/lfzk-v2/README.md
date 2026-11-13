# Longfellow V2: extraction, soundness and zero knowledge

The current numbered-strand soundness endpoint is
[`Mdoc.Soundness.averaged_ratio_le`](LfzkV2/Current/Mdoc/Soundness.lean).
It connects one SHA oracle, the original raw adversarial query log, the
complete serialized proof, the runtime verifier and the first-context
paired extractor. Its conclusion is ordinary hash-witness validity and
signature-circuit satisfaction at the submitted request's public inputs,
using the same extracted pair. The complete numbered-strand privacy endpoint is
[`Mdoc.ZeroKnowledge.statClose`](LfzkV2/Current/Mdoc/ZeroKnowledge.lean).
The [assumptions](../README.md#assumptions-and-remaining-correspondence-obligations)
state the oracle, sampling and implementation boundaries.

Security results use the Fiat–Shamir model. Local counting and masking
identities support that analysis. The protected Polygero paper results retain
their original public-coin statements and signatures.

## Current MAC-free protocol

The exact bound, the Polygero coefficient `c`, the strict `0.97` cap, the
all-`Q` linear bound and the mdoc approximation are stated once, in the
[formal README](../README.md#v2-extraction-soundness), together with a
top-down [proof map](../README.md#proof-map). The endpoints are
`Mdoc.Soundness.averaged_ratio_le`, `averaged_linear_ratio_le`,
`averaged_nonvacuous` and `averaged_mdoc_approximation`; the exact rational
bound is `LfzkV2.Current.Soundness.Rate7.failureBound`.

The supported one-/two-/three-/four-attribute compiler shapes have respectively
488/492/497/500 rounds. `MdocRoundShape.rounds_eq` derives the total from each
per-layer schedule; `scripts/check_mdoc_round_shapes.py` checks those schedules
against the current Rust compiler. The approximation takes a supported-shape
witness and derives the round bound internally.

`r` counts rounds: one per `begin_squeeze()` call, regardless of the number of challenge draws within that round. The final seal has its own two-query
finalization. Proof bytes and public requests may be chosen adaptively.
Repeated inputs receive the same answer. Probability covers the ideal SHA
oracle and arbitrary finite private random choices.
[`Mdoc.RuntimeSoundness.ratio_le`](LfzkV2/Current/Mdoc/RuntimeSoundness.lean)
handles each fixed public setup.
[`Mdoc.OracleSoundness`](LfzkV2/Current/Mdoc/OracleSoundness.lean) derives that setup
from the complementary slice of the same SHA function and preserves the
original output, protocol-domain query prefix and complete verifier replay.
`Q` is a worst-case bound on distinct inputs in the full original byte-oracle
trace, for every private coin and every total oracle; repetitions count once.
The residual trace merely filters that log. The averaged API permits the same
finite coin to choose both the complementary setup slice and the adversary,
including correlation between them. This coin is independent of the fresh
protocol-domain oracle. Setup conditioning adds no error term.

`RuntimeVerifier.Public.polynomialX` is the polynomial-basis element encoded
as integer 2, before the fixed adapter exponent is applied. Checked decoding
validates its multiplicative order and derives the conversion generator from
that power. The quotient-base identities remain available as component lemmas.

The ordinary rate-1/7 profile is `(k,s,n,t)=(349,12,2443,84)`. Its
[exact Hahn certificate](LfzkV2/Current/Parameters/Rate7.lean) and list bounds
are checked internally. The theorem derives verifier acceptance, application
failure coverage, query charging, the role maximum, and one shared Merkle
explanation. The proof derives execution correspondence, failure coverage and coding-error
budgets internally. The approved ideal joint sampling law remains an explicit
assumption.

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
[`Soundness.Composition.soundness`](LfzkV2/Current/Soundness/Composition.lean) theorem handles
other trusted setups; the mdoc endpoint takes no independent advice decoder,
metadata callback, transcript plan or backend-layout certificate.
The concrete mdoc topology supports a hash component strictly deeper than its
adapter; this ordinary depth restriction is explicit in its setup bounds.
The current hash and adapter have respectively 20 and 12 layers. The general
layered-sumcheck model still supports components in either depth order and ties.

### Oracle and implementation boundary

One classical ideal SHA oracle supplies setup hashes, strand nodes,
counter-indexed PRF outputs, indexed Merkle hashes and the final seal.
The node/PRF byte syntax and the literal Merkle/setup tags separate their
domains. `StrandDomains` proves that complete verifier replay stays in the
protocol domain. `setup_merge` and `parameters_merge` identify public
metadata computed through that same oracle. Conditioning on complementary
answers and averaging them adds zero error.

Requested role blocks satisfy the approved ideal joint sampling law.
[`StrandRoleSampling`](LfzkV2/Current/StrandRoleSampling.lean) and
[`StrandSampling`](LfzkV2/Current/StrandSampling.lean) retain all coordinates
within one round together. Nonzero field elements and ordered openings have
their specified distributions. Rejected bytes are outside the requested
analysis. The scalar codecs, field laws, trusted circuits and public layout
bounds are explicit. Source audit and tests connect Rust to this mathematical
verifier; mechanized Rust refinement and extractor complexity remain open.

The [shared finite-table algebra](LfzkV2/Current/SHAProbability.lean) owns
oracle-coordinate splitting, window inclusion and finite extension. The
current ZK statistical-distance lifts and soundness bounds reuse these maps.
The original submitted proof, protocol-domain query prefix and complete
verifier replay are preserved by the numbered-strand oracle transport.

### Runtime and transcript

The selected joint boundary belongs to `runtime::v2::zk`, in `runtime/v2/zk`.
Witness selection and Polygero are sibling protocols underneath it. Mdoc
provides the prime-field handoff and the generated binary adapter.

| Boundary | Data bound before the challenge | Answer block |
|---|---|---|
| Witness selection | Joint root, field identities and layouts | Two independent full coefficient vectors per field |
| Prime layered sumcheck | Public prime inputs and preceding masked messages | Shared assertion/entry coefficients, ordinary rounds, nonzero terminals and combine coefficients |
| Prime row batching | All compiled rows and final input equation | One independent weight per row |
| Rescaling | Preceding prime frontend messages and rescaling domain | One nonzero prime scalar |
| Conversion | Masked opening `mu` and conversion domain | Two nonzero prime scalars in one answer |
| Binary layered sumcheck | Masked quotient advice and public statements | One shared sumcheck over all quad fragments |
| Packing | Caller statement, public cell counts and trace-zero vector `U` | One full-field vector; absent for degree one |
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
one-/two-/three-/four-attribute presentations have respectively 488/492/497/500
ordinary boundaries. The Rust `test_all_next_zk` test counts actual
`begin_squeeze()` calls in both the complete prover and verifier and checks
these values independently of the geometry-derived schedule. Finalization
then uses a strand-node query and a seal PRF query. Binding source circuit identifiers
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
[`StrandAcceptedPath.point_canonical`](LfzkV2/Current/StrandAcceptedPath.lean)
proves that the actual reconstructed path lies in that canonical image.
[`StrandCutObservation`](LfzkV2/Current/StrandCutObservation.lean) preserves the
original first-context Merkle extractor when transporting the oracle program.
[`MerkleWireCodec`](LfzkV2/Current/MerkleWireCodec.lean) constructs exact leaf/node
preimages and their role decoders; injectivity is proved from their parsers.

[`CanonicalRuntime.decoded_true_at_request`](LfzkV2/Current/CanonicalRuntime.lean)
derives both circuit satisfactions at the actual requested public vectors from
the same extracted pair. The binary conclusion covers the generated
hash/adapter circuit; its adapter product semantics are proved. The prime
conclusion covers the trusted signature circuit, with shared bits taken from
the binary witness.

[`MdocWitness.valid_at_request`](LfzkV2/Current/MdocWitnessRequest.lean)
composes this readback with
[`HashSeparation`](LfzkV2/Current/HashSeparation.lean): a static sparse-read
certificate excludes the reserved mask/OTP suffix and generated adapter wires
from ordinary hash gates, assertions and carried outputs. It implies
`MdocWitness.HashNoninterference` and removes challenge dependence from the
ordinary hash predicate. `Mdoc.Soundness.event` states actual acceptance with
failure of the original-cut extractor to produce an application-valid witness;
its probability bounds use this bridge. The separation certificate is a Lean
premise corresponding to the compiler's test-only separation checks, with no
additional runtime work. Application-circuit correctness remains trusted.

The extractor is a mathematical finite search. No efficient enumeration bound
is claimed for the worst-case binary/prime candidate caps
`21898356682154715916` and `451457457136012100305`. The theorem establishes
extractor soundness; the separate complete privacy theorem follows below.

The default build checks the current tests and endpoint axioms, allowing only
`propext`, `Classical.choice` and `Quot.sound`. V1 proofs and shared component
algebra remain in their original namespaces.

### Current numbered-strand zero knowledge

[`Mdoc.ZeroKnowledge.statClose`](LfzkV2/Current/Mdoc/ZeroKnowledge.lean)
proves that the complete real and witness-free simulated views under one SHA
random oracle differ by at most `(Qpre+Qpost)/2^256`. Public setup, component
contexts and metadata are computed from this same oracle. The compared views
retain both raw query/answer traces, arbitrary private context, the adaptive
request, the canonical proof or failure, and the final seal. The budgets count
raw calls, including repetitions, before and after the proof.

The module boundaries follow
`Real ≈ Ghost ≡ Sim`. `StrandCanonicalExperiments` defines all three views;
`StrandCanonicalExactSimulation.ghost_sameDistribution` proves the exact
ghost/simulator equality, and `StrandCanonicalCommitmentHiding` supplies the
single statistical commitment hop. `StrandCanonicalHiding` composes them.
`StrandCanonicalExecution` contains the honest program shared with completeness,
and `StrandCanonicalContext` supplies its public configuration and actual oracle.
The analysis-only swap checks all actual leaves; the simulator's guard checks
only disclosed leaf addresses. Both retain failure outcomes and full traces.

The proof derives a fixed all-branch support for actual setup evaluation,
protocol execution and both observers. Outside answers cannot affect either
experiment. Only disclosed leaf answers are programmed; prior-query conflicts
retain the original oracle. The simulator has no witness or execution
certificate, and there is no digest-collision loss. The witness policy depends
on the full context retained by the prior observer; contexts with identical
public requests may choose different witnesses. The selected witness must satisfy ordinary `MdocWitness.HashValid` and the signature circuit only
at contexts reached by the prior observer under setup derived from that same
oracle; unreachable policy branches impose no validity obligation. The separate static
`MdocWitness.ReadDisjoint` certificate derives noninterference of ordinary hash
checks under all reserved mask/OTP assignments and generated-adapter parameters,
uniformly over public inputs and private values. The basis/generator checks,
trusted circuits/fields/codecs, and independent uniform private coins remain
explicit premises.

[`Mdoc.VerifierPrivacy.acceptance_probability`](LfzkV2/Current/Mdoc/VerifierPrivacy.lean)
specializes the comparison to the actual indexed runtime verifier. Its observer
returns exactly the runtime decision, including sampling failures, tuple
Merkle authentication and the final seal. Simulator aborts are rejecting
outcomes, not excluded executions. Verification calls count in `Qpost` when
this observer is used.

[`statClose_at_query_budget`](LfzkV2/Current/Mdoc/ZeroKnowledge.lean)
proves error at most `2^-128` when `Qpre+Qpost <= 2^128`. This is conditional on
the ideal oracle and private-randomness model; it is not a numerical SHA-256
security claim. Machine-level Rust refinement and formal running-time bounds
are outside these results. All endpoint axiom guards permit only `propext`,
`Classical.choice` and `Quot.sound`.

## Shared component results

The `LfzkV2.Current` barrel exposes application soundness, numbered-strand
privacy, verifier acceptance privacy and honest-runtime acceptance. Sampling,
metadata readback, generic oracle transport and paper-facing Merkle components
remain available through their own modules.

The runtime reuses the generic sumcheck, dual-packing, witness-selection and
Polygero libraries. The [paper-facing Polygero development](../polygero/README.md)
and its public-coin extraction/soundness theorems are preserved. The generic
[`PolygeroZk`](LfzkV2/PolygeroZk.lean) masking and distribution couplings and
finite-query Merkle hiding/preparation theorems also remain available.

`CircuitAlgebra`, `LayerMessages`, `InputBinding`, `ChallengeTests`,
`ChallengePrefix` and `ReplayPrimitives` own definitions shared by the current
runtime and standalone circuit models. The current endpoints exclude the
older `Circuit`, `Soundness`, `AssertedSoundness` and `Program` proof modules;
their paper-facing APIs remain directly importable. The source audit checks
this boundary through the full production import closures.

Some shared algebra retains its existing `Native`, `Linear` or `Layered`
namespace because the current verifier imports those definitions. The public
V2 entrypoints and API audit cover the current numbered-strand implementation.
Superseded implementation-specific transcript/extraction endpoints and the
whole-answer mdoc simulator have been removed.

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

The soundness implementation separates transport and recovered-path algebra
in [`Soundness.Transport`](LfzkV2/Current/Soundness/Transport.lean)
from the common stopped cost and deterministic cover in
[`Soundness.StoppedCosts`](LfzkV2/Current/Soundness/StoppedCosts.lean).
[`Soundness.Runtime`](LfzkV2/Current/Soundness/Runtime.lean) applies both the direct
linear bound and the optional saturated bound, then averages residuals and
transports back to raw SHA. Current parameter and
runtime adapters live under `Current.Soundness`, while the generic `Survival`
query-step calculus has no V1 or V2 implementation dependencies. Shared finite
probability and statistical-distance arguments live in `Bcs`.

`Mdoc.Soundness.averaged_linear_ratio_le` gives the leading bound for all Q,
using the same runtime stopped cost and failure cover as `averaged_ratio_le`.
The generic `SharedBudget.linear_le` has no `p*Q ≤ 1` premise. Generic audit
and count facts are in `ChronologicalAudit`, `History`, `QueryBudget` and
`StoppedSearch`; the numerical W refinement is isolated in `Hybrid` and `HistoryBounds`.
