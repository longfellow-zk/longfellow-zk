# Formal security claims and audit

## Numbered-strand soundness

The checked current endpoint is
[`MdocStrandOracle.averaged_ratio_le`](lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean).
For every `0 <= Q < 2^127`, a finite classical adaptive adversary making at most
`Q` distinct original SHA queries has accepted-extraction-failure probability

$$
\begin{aligned}
P_{\mathrm{fail}}(Q)
&\le \frac{cQ}{q}
 + \left(1-\frac{c(q-1)}{2q}\right)
   \left[1-\left(1-\frac{2}{q-1}\right)^Q\right] \\
&\quad + \frac{\binom Q2+r+15}{q^2},
\qquad q=2^{128}.
\end{aligned}
$$

`c = q * Survival.Rate7.parentBudget` exactly; the [formal README](README.md)
expands this rational in binomial coefficients and field orders.
`MdocStrandOracle.averaged_nonvacuous` proves failure probability
**strictly less than 0.97** for `Q < 2^127` (cap rounded up to two decimal places).
The primary endpoint names replace the earlier linear theorems; the obsolete
linear accounting chain is removed. No execution or charging certificate is
added to the mdoc endpoint.

`r` counts rounds, one per `begin_squeeze()` call. The rate-1/7 certificate fixes
`(k,s,n,t)=(349,12,2443,84)`. Both fields share one indexed Merkle tree and
one extracted tuple from the original commitment cut.

The proof path has the following checked boundaries.

1. `StrandRecovery.accepted_recovery_or_hash` recovers ordered strand
   queries, the actual PRF rows and agreement on opened columns, or charges
   a hash event.
2. `StrandProtocol.accepted_decoded` transports successful physical role
   reads to the same normalized application and statement.
3. `Joint.Family.verify_of_indexedAgreement` transfers all backend checks
   together to the tuple extracted from the original cut.
4. `StrandCharges.localProof_single_cache` identifies actual accepted-path
   tests with the chronological cache, including the original commitment cut.
   `Survival.QueryStep.step_le` bounds each transparent test or opaque step.
5. `StrandProtocol.recovered_stopped_charge` retains the original Polygero
   weights on the stopped trace. `conditioned_cost_mean_le` assigns backend
   and auxiliary hash costs to disjoint opaque query slots. Residuals are
   averaged before applying the raw seal/Merkle exception bound.
6. `MdocStrandSoundness.ratio_le` constructs the concrete rate profile,
   metadata, layout, advice decoder and complete-proof parser.
7. `MdocStrandOracle` uses the same SHA function for setup and execution.
   `setup_merge` and `parameters_merge` preserve public data.
   `submitted_output`, `original_trace`, `verifier_actual` and
   `event_verified` identify the original output, filtered original log
   and actual complete verifier. The complementary oracle marginal is
   averaged with zero additional error.

The input includes trusted circuit descriptions, canonical field codecs,
static capacity bounds and the approved ideal joint role sampler. Runtime
acceptance, query order, column agreement and the final failure cover are
derived. Axiom checks on the endpoint and correspondence lemmas report only
`propext`, `Classical.choice` and `Quot.sound`.

The oracle assumption is a classical ideal SHA oracle with uniform
independent answers at distinct byte inputs and consistent repeated answers.
The role-block sampling law includes nonzero elements and openings without
replacement. Rejected bytes are outside the requested analysis. See the
[full model boundary](README.md#assumptions-and-remaining-correspondence-obligations)
for trusted circuit/field inputs, finite-search extraction and Rust source
correspondence.

## Validation and architecture

Three review passes cover the current soundness path.

1. The mathematical review checks acceptance, the original extraction cut,
   ordered recovery, authenticated column agreement, shared-budget charging
   and the final one-oracle bound. Endpoint axiom guards check for additional
   logical assumptions.
2. The architecture review puts oracle windows, observers, SHA domain routing
   and finite probability calculations in shared modules. Soundness has no
   dependency on the ZK assembly. Trace-only replay lemmas avoid reconstructing
   the verifier result and application bookkeeping to establish acceptance or
   decoding. Generic algebra and paper-facing component lemmas retain their contracts.
3. The implementation review compares numbered strand and PRF framing,
   little-endian indices, indexed Merkle leaves and nodes, 32-byte nonces,
   canonical proof parsing and the mandatory final seal with Rust. The Rust
   transcript and adapter bind prover messages and static statements while
   retaining challenge-derived coefficients in verifier state.

The endpoint tests and the 610 native Rust library tests pass. This is a
source-correspondence audit. The v2 test aggregate, including its preserved
shared component libraries, builds successfully. Superseded implementation proof paths have been removed
from its imports. `WholeAnswerMerkle` names the earlier unindexed node syntax
explicitly, sharing leaf encoding and physical row maps with the indexed
codec. The current soundness endpoint imports neither this historical codec
nor the ZK assembly. Numbered strand tests cover the current PRF keys.
The numbered-strand privacy proof is separate from this soundness argument.

The current indexed runtime also checks that each arithmetic response is
zero on its logical mask prefix. `StrandVerifier.prefixZeros` includes this
deterministic check for both fields; `BackendPrefix.payload_random` proves it
for honest responses. Soundness retains the existing Polygero verifier as a
weaker algebraic predicate, preserving the paper-facing component contracts.

## Zero-knowledge boundary

`MdocStrandZeroKnowledge.statClose` assembles the complete canonical-view
privacy bound, including public setup derived from one shared uniform raw
byte oracle. Independent oracle answers, fresh 256-bit nonces and honest
private coins give statistical distance at most
`(Qpre+Qpost)/2^256` from the public simulation. Both raw observer traces,
adaptive requests, reader/conflict failure branches, canonical proof and
final seal are retained. `Qpre` and `Qpost` are call bounds, not bounds on
distinct inputs.

The proof identifies the nonce-independent canonical stage with the generic
indexed hiding schedule (`stage_eq`). It proves that response-adaptive
openings read original committed columns (`disclosed_respondHonest`) and
that ghost completion is precisely the existing canonical completed view
(`complete_prepared`, `ghost_eq`). One leaf-hiding hop is then followed by
the exact frontend/backend bijection. The latter is applied independently
at each fixed oracle/ghost-label/nonce tape, preserving the prior-query
conflict decision and the installed opened-only oracle. It adds zero error.
No PRF or final-seal answer is programmed, and no collision-free-output
assumption is used.

The interfaces expose this as `Real ≈ Ghost ≡ Sim`.
`StrandCanonicalContext` and `StrandCanonicalExecution` contain the public
oracle context and honest execution shared with completeness.
`StrandCanonicalPrograms` and `StrandCanonicalExperiments` define the guarded
honest/public views and the three experiments before either privacy hop.
`StrandCanonicalExactSimulation.simulationEquiv` names the joint coin change;
`ghost_simulator_view` proves pointwise equality under it, and
`ghost_sameDistribution` states exact distributional equality.
`StrandCanonicalCommitmentHiding` proves only the statistical Real-to-Ghost
step; `StrandCanonicalHiding` assembles the two steps and raw-oracle transport.
The old qualified entry points are aliases of the declarations at their new
logical homes. In particular, the exact branch does not import the statistical
commitment theorem. The finite leaf-oracle data lives in `StrandLeafOracle`.

The public simulator has no witness or satisfaction-certificate argument.
The theorem assumes ordinary hash/signature witness satisfaction only for
contexts reached by the prior observer under setup derived from the same
oracle. Unreachable policy branches impose no validity obligation. The separate static
`MdocWitness.HashNoninterference` circuit premise preserves ordinary hash
checks for every reserved mask/OTP assignment and generated-adapter parameter,
uniformly over public inputs and private values. These premises and the
explicit basis/generator checks derive backend truth inside the coupling. The leaf-table
permutation preserves actual earlier query/answer traces, including bad
branches, and does not require a finite type of all byte strings.

The current hash compiler appends the mask/OTP suffix after application
compilation. Tests reject any hash input gate or assertion that reads this
suffix in all four compiled circuit shapes; generated adapter coefficients
belong to a separate circuit. The mask has no binary range assertion, since
`Handoff.product_handoff` already covers arbitrary mask bits modulo the prime.
This removes the conflict between mask canonicality and the unrestricted
noninterference premise. The test-only check costs nothing at runtime and is
not a kernel proof of the Rust-to-Lean circuit correspondence.

`StrandCanonicalHiding.statClose` first fixes the complementary non-leaf
oracle. `StrandLeafWindow.statClose_of_extension` reindexes the finite leaf
table to its raw byte addresses and averages over complementary coordinates
arising from the complete window, without adding an error term. This preserves
setup consistency when applying the reached-witness premise.
`StrandCanonicalByteSupport` derives the support of the actual honest and
simulated executions: all typed numbered-strand histories and PRF counters,
all indexed Merkle preimages, and all observer branches. Only contexts
reachable in the prior observer are enumerated; its private state need not
be a finite type. `real_extend` and `simulate_extend` prove pointwise that
answers outside this fixed support cannot affect either complete view,
including programmed-leaf and failure branches. No support certificate or
execution hypothesis is passed to the theorem.

Axiom guards on every new bridge and composition endpoint allow only
`propext`, `Classical.choice` and `Quot.sound`. No recursion/heartbeat limit
was raised. The generic leaf-table lift accepts the caller's equality
decision, avoiding normalization of two different function-space enumerations.
Finite supports are used through membership lemmas rather than expanding
their exhaustive enumerations during theorem matching.

`StrandMdocSetup` covers the leaf domains for every digest-selected public
setup. Domain separation proves that varying these coordinates preserves
setup and metadata. `StrandMdocSetupSupport.program_result` identifies the
four actual setup hash calls, including the joint-context preimage selected
by earlier answers. Their finite support is included in the complete window.
`MdocStrandZeroKnowledge.real_extend` and `simulate_extend` establish the
pointwise support property for the setup-derived experiments themselves.
Averaging the complementary coordinates adds no error. The concrete budget
corollary proves error at most `2^-128` at `2^128` total raw observer calls.

`StrandVerifierObserver.observe_result` and `optional_result` identify a
raw-query observer with the actual indexed runtime verifier. Metadata is
reconstructed from the public setup values and proved equal to the actual
metadata. `MdocStrandVerifierPrivacy.acceptance_probability` bounds the
difference in actual acceptance probabilities by the same privacy error;
rejection and abort outcomes are retained. No successful-verifier or
always-accepting-simulator premise is used.

The theorem uses a fixed witness policy, valid at actually reached requests,
with separate static hash noninterference, signature satisfaction,
basis/generator checks, and trusted field/codec/circuit/layout inputs. Honest private coins and 256-bit
nonces are independent and uniform. It assumes a classical SHA random oracle,
not a numerical concrete-SHA indistinguishability bound. Rust correspondence
is reviewed rather than mechanically refined, and no machine-cost theorem
is claimed. V1 proofs and generic paper-facing component theorems are preserved.

## Checked endpoints and components

| Result | Endpoint | Scope |
| --- | --- | --- |
| Current V2 extraction soundness | [`MdocStrandOracle.averaged_ratio_le`](lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean) | Exact parameter-dependent bound for the actual numbered-strand event. |
| Current V2 uniform soundness cap | [`MdocStrandOracle.averaged_nonvacuous`](lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean) | Strictly below 0.97 for `Q < 2^127`. |
| Current V2 statistical zero knowledge | [`MdocStrandZeroKnowledge.statClose`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocStrandZeroKnowledge.lean) | Complete current indexed runtime view, error `(Qpre+Qpost)/2^256`. |
| Actual verifier privacy | [`MdocStrandVerifierPrivacy.acceptance_probability`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/MdocStrandVerifierPrivacy.lean) | The actual verifier decision, including rejection and abort. |
| Extant V1 runtime | [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) | V1 signature/hash extraction and soundness certificates. |
| Paper-facing Polygero | [Polygero component library](polygero/README.md) | Original public-coin extraction/soundness and generic algebra, preserved unchanged. |
| Packing and witness selection | [Dual packing](dual-packing/README.md), [witness selection](witness-selection/README.md) | Current component reductions and shared algebra. |

Implementation-specific V2 checkpoint endpoints and the earlier whole-answer
mdoc simulator have been removed. Shared definitions required by current
verifier/decoder/completeness proofs remain in their existing namespaces.
Generic Polygero, Merkle coupling, sumcheck, masking and parameter statements
are preserved. Source correspondence and trusted field/circuit/sampling
premises remain explicit; the kernel does not certify Rust machine semantics.

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

The default V2 API imports only the current implementation and surviving
shared components. Its axiom audit covers every imported V2 declaration,
including private helpers, rather than a historical endpoint whitelist.

The V1 Rust inspectors load the frozen archives through the current
single-crate runtime, recompute archive and circuit IDs, compare the five
recorded circuit/geometry profiles, and reject violations of the structural
assertion premises. The older Python launchers targeting the former crate
layout have been removed. The remaining legacy numerical reporting scripts
do not participate in the trusted Lean proof chain.
