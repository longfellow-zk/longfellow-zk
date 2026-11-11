# V2 transcript and SHA-256 strands

The numbered-strand soundness endpoint is
[`MdocStrandOracle.averaged_ratio_le`](../lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean).
It uses one SHA oracle for setup, original adversarial calls, transcript
nodes, indexed PRF blocks, indexed Merkle authentication and the final seal.
The complete indexed ZK endpoint is
`MdocStrandZeroKnowledge.statClose`.
The [security audit](../AUDIT.md) states the oracle and implementation scope.

## Composition interfaces

[`Composition`](TranscriptV2/Composition.lean) separates protocol algebra from
transcript realization. `LocalCharges` records nonnegative single-answer and
adjacent-pair charges, their independence from the coordinates being sampled,
and their local averages. Charges sharing a role are added before taking the
maximum over roles. All local reductions use the same selected binary/prime
witness pair.

`SoundnessRealization` requires equality of the complete observation law,
including the verifier's decision and the extractor's actual cut. An accepted
execution outside explicit exceptions must yield the queried logical path or
a speculative-query charge. Its generic theorem gives `epsilon * Q + delta`:
ordinary and speculative queries share the original adversary's budget;
`delta` accounts for the remaining exceptions. Replay cannot pay that budget.
These are obligations to instantiate, not certificates accepted from an
application. The current runtime uses the survival specialization below.

The current runtime uses the saturated specialization in
[`Survival.QueryStep`](../survival/Survival/QueryStep.lean) and
[`Survival.ChargeMonitor`](../survival/Survival/ChargeMonitor.lean).
Transparent local tests are fixed from a chronological cache. The audit stops
at their first escape; Polygero and hash costs are paid by disjoint opaque
slots reached before stopping. Their weights retain the original commitment
cut. The final current endpoint replaces the linear query factor by

$$
\frac{cQ}{q}+\left(1-\frac{c(q-1)}{2q}\right)
\left[1-\left(1-\frac{2}{q-1}\right)^Q\right],\qquad q=2^{128}.
$$

Here `c=q*Survival.Rate7.parentBudget` is the exact current Polygero coefficient,
approximately `1.0000012312149082441647508747`. Including the hash correction,
the full failure probability is **strictly less than 0.97** for `Q < 2^127`.
The [formal README](../README.md) gives the exact coefficient and the convenient
mdoc approximation for every nonnegative query budget.

[`Simulation`](TranscriptV2/Simulation.lean) supplies the separate ZK interface.
`BoundaryCoupling` preserves the state needed by later stages; its composition
laws add the errors. `ProgrammingRealization` concerns the complete executed
observer view, including retained context, the proof and pre/post query traces.
Programming must preserve earlier answers and proof-implied hashes. The
observer can keep querying the returned oracle; it is not given the oracle's
entire table.

## SHA-256 strand model

The direct model records actual SHA calls in adaptive query trees:

| Modules | Responsibility |
| --- | --- |
| [`StrandEncoding`](TranscriptV2/StrandEncoding.lean), [`Strand`](TranscriptV2/Strand.lean) | Canonical node/PRF domains, numbered continuation and counter bounds. |
| [`StrandReader`](TranscriptV2/StrandReader.lean), [`StrandTranscript`](TranscriptV2/StrandTranscript.lean) | Segmented byte reads, message frames, round labels and complete-body finalization. |
| [`StrandOracle`](TranscriptV2/StrandOracle.lean), [`StrandCoupling`](TranscriptV2/StrandCoupling.lean) | Exact raw-oracle restriction and grouping of counter blocks into a digest's PRF stream. |
| [`StrandReplay`](TranscriptV2/StrandReplay.lean), [`StrandTrace`](TranscriptV2/StrandTrace.lean), [`StrandInventory`](TranscriptV2/StrandInventory.lean) | One retained cache across search and replay, with the actual query that first supplied each stream. |
| [`StrandUnfolding`](TranscriptV2/StrandUnfolding.lean), [`FreshRenaming`](TranscriptV2/FreshRenaming.lean) | Recovery of logical histories from queried inputs and distribution-preserving online query names. |
| [`StrandCharging`](TranscriptV2/StrandCharging.lean), [`DigestCollision`](TranscriptV2/DigestCollision.lean), [`StrandSealCharging`](TranscriptV2/StrandSealCharging.lean) | Shared query charging, scoped hash collisions and guessing an unqueried final seal. |

PRF preimages are `LE32(0) || LE64(id) || digest || LE64(counter)`, exactly
52 bytes. Node preimages start with `LE32(1) || LE64(id) || LE32(parent_count)`,
followed by the parent digest, if present, and payload. The root has id zero
and no parent; each continuation has one parent and increments the id with
overflow checking. The runtime has no fork/join operations. Its distinct
positions have distinct inputs even if their digest outputs coincide.
Arbitrary adversarial SHA queries may still contain the multi-parent syntax.
Rust ownership consumes strand handles; the immutable Lean functions describe
the transitions, not borrowing.

The final seal uses two SHA queries: hash the node binding the actual canonical
proof body, then read PRF counter zero at that digest. The stored seal is this
PRF answer. It is not the node digest. Segmented reads preserve bytes and query
traces, including buffered tails and counter exhaustion.

Grouping a PRF stream does not create a second oracle. It is a restriction of
the same raw SHA table, with an exact finite-marginal product law. Reserving a
stream at its node query preserves arbitrary raw executions, including prior
PRF queries and colliding node digests; existing answers are retained. Stream
keys are `(id, digest)`, so equal digests at different positions do not share
challenge blocks.

[`StrandLinear`](TranscriptV2/StrandLinear.lean) proves that a node's input is
independent of its own hash answer. [`StrandRecovery`](TranscriptV2/StrandRecovery.lean)
recovers one target per position from the original query table and submitted
final seal. [`StrandMissingQueries.missing_density_le`](TranscriptV2/StrandMissingQueries.lean)
proves that a chain of `r` ordinary rounds with a queried final seal and no
original-query collisions has a missing node query with probability at most
`(r+1)/2^256`. The bound includes the terminal node. Its finite address window
must preserve the reached inputs; it does not assume that replay hashes are
collision-free or add replay queries to the adversary's budget.
[`StrandLinearReplay.history_replay`](../lfzk-v2/LfzkV2/Current/StrandLinearReplay.lean)
identifies this chain with the runtime encoding whenever the canonical packets
are challenge-independent. The existing concrete metadata proves that packet
property. The runtime wrapper combines this with indexed Merkle recovery and the shared
ordinary/auxiliary budget in the checked mdoc endpoint.

For speculative targets, the shared-budget lemma bounds the average by
`epsilon * E[n] + Q * E[k] / M`, where `n` and `k` count ordinary and
speculative queries and `M = 2^256`. If `n+k <= Q` and `Q/M <= epsilon`, this
is at most `epsilon * Q`. It does not add a blanket `Q^2/M` penalty for all
in-search digest guesses. Targets first matched during verifier replay have
the separate bound `R * (Q+R) / M` for singleton claims. Collisions among
eligible inputs have the sharp bound `S(S-1)/(2*M)`; PRF observations remain
in the execution even when those inputs are outside the collision scope.
Merkle and strand reductions must use one shared collision allowance.

## Runtime adapters

The current adapters use the numbered node/PRF syntax and the indexed
Merkle verifier. Their acceptance event contains the complete serialized
proof, actual verifier replay and original extraction cut.

The application-specific modules live under `LfzkV2.Current`:

| Modules | Checked connection |
| --- | --- |
| [`StrandSearch`](../lfzk-v2/LfzkV2/Current/StrandSearch.lean), [`StrandPath`](../lfzk-v2/LfzkV2/Current/StrandPath.lean), [`StrandRecognition`](../lfzk-v2/LfzkV2/Current/StrandRecognition.lean) | Actual raw query names, logical path recovery and ordinary/speculative accounting. |
| [`StrandRuntime`](../lfzk-v2/LfzkV2/Current/StrandRuntime.lean), [`StrandVerifier`](../lfzk-v2/LfzkV2/Current/StrandVerifier.lean), [`StrandAcceptedPath`](../lfzk-v2/LfzkV2/Current/StrandAcceptedPath.lean) | Canonical packets, existing arithmetic/authentication checks and acceptance with the actual PRF final seal. |
| [`StrandAuthentication`](../lfzk-v2/LfzkV2/Current/StrandAuthentication.lean), [`StrandExecution`](../lfzk-v2/LfzkV2/Current/StrandExecution.lean) | Full verifier replay and its accepting decision reconstructed from that trace. |
| [`StrandCut`](../lfzk-v2/LfzkV2/Current/StrandCut.lean), [`StrandCutObservation`](../lfzk-v2/LfzkV2/Current/StrandCutObservation.lean) | Exactly the raw prefix before the first query naming a context, with the same joint observation law as the named execution. |
| [`StrandCommitment`](../lfzk-v2/LfzkV2/Current/StrandCommitment.lean) | One cut and one extracted tuple for both fields; genuine Merkle target hits are separate from transcript-parent guesses. |
| [`StrandWindow`](../lfzk-v2/LfzkV2/Current/StrandWindow.lean) | Finite supporting address sets and exact execution transport for arbitrary raw query trees. |
| [`StrandRoleSampling`](../lfzk-v2/LfzkV2/Current/StrandRoleSampling.lean), [`StrandLocalCharges`](../lfzk-v2/LfzkV2/Current/StrandLocalCharges.lean) | Physical role factors, schedule-derived widths and the existing application charge averages. |

The full replay executes ordinary rounds, the actual tuple authentication,
the final node and the final-seal PRF. Its non-PRF query count is at most
`rounds + 1 + 2*n`, where `n` is the Merkle leaf count. Completing unused oracle
coordinates arbitrarily preserves its accepting decision. The extracted cut
contains actual non-PRF queries only; unused digest coordinates from reserved
streams cannot become commitment entries.

Application normalization preserves the existing charges for both fields'
fingerprints and sumchecks, row batching, rescaling, conversion and packing.
Its widths come from the circuit schedule. Joint Polygero single/pair
normalization and the concrete accepted-extraction cover are also checked.
The actual failure observation is connected to this cover by
`StrandProtocol.recovered_failure_charge`. Original strand speculation and
indexed Merkle receiving share an allowance of `2Q/2^256` per auxiliary
query slot. The algebraic role bound is `2/(q-1)` per ordinary slot.
`ProtocolProbability` combines these complementary slots of the original
query budget after averaging the sampler coordinates.

At the current rate-1/7 parameters, the one-SHA mdoc theorem uses the exact
parameter-dependent survival bound in the [formal README](../README.md).
For `Q < 2^127`, its failure probability is strictly below 0.97. The supported
mdoc circuit also has the all-budget approximation

$$
\Pr[\mathrm{accepted\ extraction\ failure}]
\le Q\,2^{-127}+Q^2\,2^{-257}+2^{-246},\qquad Q\ge0.
$$

`MdocStrandOracle` proves setup-domain independence, preservation of the
original submitted output and filtered log, complete verifier replay under
the same SHA function, and averaging over complementary SHA answers.

## ZK reuse and sampling scope

[`BackendAdaptiveJoint`](../lfzk-v2/LfzkV2/Current/ZeroKnowledge/BackendAdaptiveJoint.lean)
uses the fixed-opening algebra for a response-selected opening set. A public
translation of the existing `m` and `fstar` masks preserves both complete
backend responses while changing the opening set. The joint distribution
retains ordered sampling and failure; the opening challenge is not programmed.
[`BackendAdaptiveProfile`](../lfzk-v2/LfzkV2/Current/ZeroKnowledge/BackendAdaptiveProfile.lean)
specializes this coupling to the physical mdoc responses and columns.

The indexed Merkle coupling is proved in
[`StrandGhostMerkleProbability`](../lfzk-v2/LfzkV2/Current/ZeroKnowledge/StrandGhostMerkleProbability.lean).
Its byte-oracle transport and complete simulator are assembled in
[`MdocStrandZeroKnowledge`](../lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocStrandZeroKnowledge.lean).
The complete view includes shared-oracle public setup, both raw observer traces,
the proof and actual verifier observations. With 32-byte nonces its statistical
error is at most `(Qpre+Qpost)/2^256`.

The approved probability model assumes each fresh requested role block has
its specified joint uniform law: full-field coordinates, nonzero scalars and
openings without replacement. Repeated requests reuse their answer. Rejected
sampler bytes are outside the requested analysis. The conditional finite-decoder
lemmas in [`StrandSampling`](TranscriptV2/StrandSampling.lean) remain available,
but do not prove exact prime-field uniformity from a fixed finite SHA stream.
No such finite-stream claim is used to discharge the sampler assumption.
SHA is modeled as a classical ideal 256-bit random oracle on the actual
canonically separated byte domains; concrete SHA-256 is not proved ideal.

The [separate tests](TranscriptV2/Tests/Strand.lean) cover numbered syntax,
overflow, segmented reads and seal rejection. The
[missing-query tests](TranscriptV2/Tests/StrandMissingQueries.lean) check input
separation under identical digest outputs and audit the counting theorems'
axioms. The checked targets use only the standard Lean foundations. The test
aggregate includes the current runtime, complete indexed ZK theorem and
reusable generic transcript components.

## Logical oracle abstraction

This library proves adaptive oracle-query accounting for a typed transcript
with link feedback and a checked final seal. It uses the existing
`Bcs.TotalOracle` finite random-oracle model: the adversary may query arbitrary
points in any order, repeat queries, and explore branches. `Q` bounds the
number of distinct queried points. A deterministic query tree represents each
fixed choice of the prover's private randomness.

The generic logical oracle answer is a pair `(link, challenges)`. The raw
numbered-strand coupling constructs this abstraction from the same SHA table;
it does not introduce a separately seeded generator.
The challenge component can contain the whole block used by a round, including
both fingerprint vectors and the other field's coordinates.

## Representation and replay

`Chain` describes deterministic verifier replay, including reconstruction of
statements from earlier challenges. Its input representation must satisfy:

- Every successor input uniquely identifies its full parent input and the
  link claimed for that parent. This is a property of canonical framed
  preimages, not an ability to invert a hash digest.
- Successor inputs carry the actual parent answer's link.
- The rank increases at each boundary, including the separately domain-separated
  final input. Thus a proof with `R` boundary rounds has `R+1` distinct inputs.
- The final seal is the link coordinate of that final answer. The complete-proof
  representation must bind the actual canonical body, including authentication
  data, to this input.

The last body-binding requirement is part of the encoding correspondence, not
an additional conclusion of the abstract `Chain` laws. `APITest` supplies a
finite one-round instance whose final input distinguishes two different bodies.
The laws also cover zero-round proofs.

[`Recompute`](TranscriptV2/Recompute.lean) expresses verifier replay as an
oracle program and proves that it preserves the prover's output while recovering
the exact final state. It is used by the Merkle explanation adapter. Its queries
are not added to the adversary's Fiat--Shamir charging budget.

## Checked bounds

`link_guess_ratio_le` bounds out-of-order or unqueried parent links by
`Q/|Link|`. Stop the search immediately before its first query to a parent.
That stopped prefix is independent of the parent's answer. Each distinct
earlier child supplies at most one candidate link. Across all parents, a child
is counted at most once because it identifies one full parent input. Hence
the total number of guesses is at most `Q`, without a depth or birthday factor.

`final_seal_guess_ratio_le` adds at most `1/|Link|`: if the final input was not queried,
the prover's output and the verifier's reconstruction of that input are
independent of its answer. A passing seal then guesses one link.

Outside these events, `Chain.parent_queried_before` proves that each child was
queried after its parent. `Chain.required_fresh_queries` proves that a valid
seal requires at least `R+1` fresh queries. `short_search_ratio_le` bounds a
valid seal from a search below this budget by

```
epsilon_chain = (Q+1)/|Link|.
```

`Reduction` is a proof-only certificate that a failure implies a local bad
boundary and a valid final seal. It contains no query-order or query-charging assumption.
`Reduction.failure_ratio_le` derives

```
Pr[failure] <= Q*num/den + (Q+1)/|Link|,
```

when each point's bad-answer count times `den` is at most `num*|Answer|`, with
`den > 0`, and its local predicate is independent of its own answer. Integer
rounding is handled once in the shared counting lemma; adapters need no pivot
or divisibility argument. The sumcheck and witness-selection adapters
derive this independence from ancestor-dependent data using `PrefixPoints`.
`SumcheckV2.Chained.ofRoundReplay` constructs the local reduction from ordinary
sumcheck's claim/true-sum identities and evaluation updates. A false initial
claim reaching a true terminal claim must be repaired at some boundary:

- [`SumcheckV2.Chained.failure_bound`](../sumcheck-v2/SumcheckV2/ChainedFiatShamir.lean):
  `2Q/q + (Q+1)/|Link|` for ordinary quadratic sumcheck with uniform field challenges.
- [`WitnessSelection.Chained.failure_bound`](../witness-selection/WitnessSelection/ChainedFiatShamir.lean):
  `Q*choose(L,2)/q² + (Q+1)/|Link|` for a list of at most `L` projected candidates.

With a 32-byte link, `|Link|=2^256`. For multiple frontend components, use their
combined local bad event in the generic theorem so the common chain exception
is charged once. Repeated queries provide no new answer; branch exploration
uses additional distinct points. Adding chained queries changes the required
query count, not the polynomial's local bad-root bound.

[`SharedCharging`](TranscriptV2/SharedCharging.lean) combines single-answer
charges with grouped parent-first two-answer charges while retaining their
actual queried roles. Its per-point budget includes the grouped cost at each
parent, so the final bound uses the largest combined role cost and one distinct
query budget. The theorem still requires the protocol's local response counts
and the reduction of accepted failures to those charges. In particular, a
joint opening must count complete response tuples, not a single-field projection.

[`SharedReduction`](TranscriptV2/SharedReduction.lean) connects those charges
to a sealed accepted path. Its algebraic certificate supplies either a local
bad boundary or an adjacent parent/child event. Feedback proves that the parent
was queried first, outside the existing chain exception. With combined local
cost at most `epsilon` at every query role, the resulting bound is
`Q*epsilon + (Q+1)/|Link|`. The certificate does not assume an ordered query
trace. The `feedback_sum` lemma also accounts for child inputs carrying a
claimed parent link: only the matching link contributes, so the protocol's
summed response budget is preserved.

## Scope

These are conditional ROM component theorems. The
[current mdoc composition](../lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean)
instantiates the preimage laws, algebraic cover and shared query charges for
actual adaptive runtime acceptance event, including nonzero-sampling and
Polygero errors. Canonical input bytes and the first-context extractor are
connected by checked parsers and replay equalities. The oracle supplies a
uniform link and the correctly distributed joint challenge block, with
independent auxiliary randomness and consistent repeated answers. The earlier
expansion and rejection sampling were audited against this model. The direct
strand results above now provide canonical accepted-path recovery and raw
stream coupling. Joint role sampling and extractor transport remain necessary
to reuse the algebraic model for the SHA-256 runtime. This component
library alone does not establish an application's end-to-end bound.

The counting proof does not construct a timed extractor. Polygero's
statement-dependent extraction needs verifier replay of sumcheck to reconstruct
its statement. A commitment-only candidate list and early fingerprint selection
are distinct analysis objects; they do not let the backend decoder omit that
replay. Internal noncomputable definitions do not establish extractor complexity.

From `formal/`, run `lake build TranscriptV2.APITest`. The API tests cover
body binding, a guessed seal with no queries, an out-of-order guessed link,
an ordinary ordered execution, the required fresh-query count, and enforce the
foundational-axiom lists of the bounds. Protocol adapters have their own API tests.
