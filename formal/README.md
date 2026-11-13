# Formal verification

## V2 extraction soundness

The numbered SHA-256 strand verifier has a checked Fiat–Shamir extraction
bound at the current mdoc rate-1/7 parameters. For every integer `0 <= Q < 2^127`,
consider any finite classical adaptive adversary making at most `Q` distinct
original SHA queries.

Let $P_{\mathrm{fail}}$ denote the probability that the verifier accepts
and the paired extractor fails to recover a witness satisfying the ordinary
hash constraints and signature circuit at the actual requested public inputs.
Both use the same selected pair. Then

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

For every `Q < 2^127`, the full soundness failure probability is
**strictly less than 0.97**, with the cap rounded up to two decimal places.
`Mdoc.Soundness.averaged_nonvacuous` proves this strict conclusion. The primary
`ratio_le` and `averaged_ratio_le` endpoints use the exact `LfzkV2.Current.Soundness.Rate7.failureBound` above.

The exact parameter-dependent Polygero coefficient is

$$
c=\frac{C}{q^{12}}+\frac{qC}{\ell^{13}}
  +\left(1+\frac q\ell\right)\left(1+(L-1)T\right),
$$

where

$$
\begin{gathered}
C=\binom{2443}{374},\qquad T=\frac{\binom{866}{84}}{\binom{2443}{84}},\\
L=1272737905242889781956743699885451,\\
\ell=2^{256}-2^{224}+2^{192}+2^{96}-1.
\end{gathered}
$$

Thus $c=1.0000012312149082441647508747\ldots$, and Polygero is charged at exactly $c/q$. Lean defines this rational as
`LfzkV2.Current.Soundness.Rate7.polygeroConstant` and checks
`1.00000123121490824416 < c < 1.00000123121490824417`.
The complementary coefficient `1-c*(q-1)/(2*q)` follows from the shared-query
survival argument.

A convenient approximation for the mdoc circuit, valid for every $Q\ge0$, is

$$
P_{\mathrm{fail}}(Q)\le Q\,2^{-127}+Q^2\,2^{-257}+2^{-246}.
$$

The largest supported mdoc circuit (four attributes) has 500 rounds:
`275 + 125 + 3*(20 + 11) + 7 = 500`. Thus `r+15 = 515 < 2^10`.
The proof rounds the constant correction up to $2^{-246}$.
`Mdoc.Soundness.averaged_mdoc_approximation` proves this all-budget consequence.

The supported one-/two-/three-/four-attribute compiler shapes have respectively
488/492/497/500 rounds. `MdocRoundShape.rounds_eq` derives the total from each
per-layer schedule; `scripts/check_mdoc_round_shapes.py` checks those schedules
against the current Rust compiler. The approximation takes a supported-shape
witness and derives the round bound internally.

Here `r` is the number of rounds: one per `begin_squeeze()` call. The final seal
is counted separately. The numerical composition bound reads its geometry,
list capacities and field orders from the active certificate and parameter
modules. The generic profile interface bounds local charges by the shared
role maximum; the production theorem retains the exact Polygero coefficient
shown above. The certified parameters are
`(k,s,n,t)=(349,12,2443,84)`; the indexed Merkle heap has depth 12.
The bound includes arbitrary query repetitions and `Q = 0`. Its exact
`q - 1` denominator retains the nonzero-sampling correction.

[`Mdoc.Soundness.averaged_ratio_le`](lfzk-v2/LfzkV2/Current/Mdoc/Soundness.lean)
is the one-SHA endpoint. Arbitrary serialized proofs pass through the
complete-proof parser. Public setup hashes, ordinary strand nodes, indexed
PRF blocks, Merkle authentication and the final seal use the same byte
oracle. Setup answers are in a disjoint complementary domain. The theorem
holds for every fixed complementary slice. The averaged API uses a finite coin
that may jointly determine that slice and the adversary; these choices can be
correlated with each other and are independent of the remaining fresh protocol
oracle. `Q` bounds distinct inputs in the original adversary's full byte-oracle
trace for every coin and every total byte oracle. It is a worst-case bound,
including queries outside the protocol domain; repetitions count once.
Conditioning on setup answers and filtering the trace introduce no extra loss.

The endpoint constructs the mdoc metadata, quotient-advice decoder, layout,
frontend plans and rate certificate. `submitted_output`, `original_trace`,
`verifier_actual`, `event_verified`, `setup_merge` and `parameters_merge`
connect its event to the original submitted proof, original query log and
complete runtime verifier. The extractor scans the original protocol-domain
prefix at the commitment cut. Both fields use the same extracted tuple.
Runtime acceptance, ordered query recovery, column agreement and algebraic
failure coverage are proved internally.

The [pencil-and-paper argument](survival/README.md) describes the complete assembly.

The leading shared-budget theorem is also available for every $Q\ge0$:

$$
P_{\mathrm{fail}}(Q)\le
\frac{2Q}{2^{128}-1}+\frac{\binom Q2+r+15}{2^{256}}.
$$

`Mdoc.Soundness.averaged_linear_ratio_le` proves it directly from the same
stopped search, common-witness cover and retained cost as the saturated bound.
The generic linear theorem has no restriction $pQ\le1$; that restriction is
needed only by the optional saturation argument. For $Q\ge2^{127}$ the
concrete endpoint extends the linear bound using probability being at most one.

`Mdoc.Soundness.averaged_polynomial_ratio_le` restates the linear bound in
polynomial form, also for every $Q\ge0$:

$$
P_{\mathrm{fail}}(Q)\le 2Q\,2^{-128}
 + \left(\frac{2Q^2}{1-2^{-128}}+r+15\right)2^{-256}.
$$

### Proof map

Read the chain top-down; each row is proved from the rows below it. The
linear and saturated bounds differ only in the survival estimate applied at
row 5; every other row is shared.

| # | Declaration | Module | Step |
|---|---|---|---|
| 1 | `Mdoc.Soundness.averaged_ratio_le` | [`Mdoc.Soundness`](lfzk-v2/LfzkV2/Current/Mdoc/Soundness.lean) | `event_implies_extraction_failure`: an accepted proof whose extracted pair is not valid for the hash and signature circuits at the request (`MdocWitness.valid_at_request`) is a row-2 event. |
| 2 | `Mdoc.OracleSoundness.averaged_ratio_le` | [`Mdoc.OracleSoundness`](lfzk-v2/LfzkV2/Current/Mdoc/OracleSoundness.lean) | Fixes the complementary setup slice (`setup_merge`, `residual_budget`, `event_eq`) and averages it and the adversary coin with no extra error. Domains: [`StrandDomains`](lfzk-v2/LfzkV2/Current/StrandDomains.lean), [`SHAOracle`](lfzk-v2/LfzkV2/Current/SHAOracle.lean), [`StrandRoutedObserver`](lfzk-v2/LfzkV2/Current/StrandRoutedObserver.lean). |
| 3 | `Mdoc.RuntimeSoundness.ratio_le` | [`Mdoc.RuntimeSoundness`](lfzk-v2/LfzkV2/Current/Mdoc/RuntimeSoundness.lean) | Builds the concrete `Soundness.Setup` and discharges the numerical premises with [`Soundness.RuntimeRate7`](lfzk-v2/LfzkV2/Current/Soundness/RuntimeRate7.lean) and [`Soundness.Rate7`](lfzk-v2/LfzkV2/Current/Soundness/Rate7.lean). |
| 4 | `Soundness.Composition.soundness` | [`Soundness.Composition`](lfzk-v2/LfzkV2/Current/Soundness/Composition.lean) | Transports raw SHA to named queries (`OracleTransport.observation_law`) and adds the hash exception (`Recovery.hashException_ratio_le`, [`Soundness.OracleBounds`](lfzk-v2/LfzkV2/Current/Soundness/OracleBounds.lean)). |
| 5 | `Soundness.Runtime.named_saturated_failure_le` | [`Soundness.Runtime`](lfzk-v2/LfzkV2/Current/Soundness/Runtime.lean) | Averages sampler residuals. Per residual, `Survival.CausalCharges.failure_le_support` (saturated, [`Survival.Hybrid`](survival/Survival/Hybrid.lean)) or `linear_failure_le_support` ([`Survival.SharedBudget`](survival/Survival/SharedBudget.lean)) turns rows 6 and 7 into a probability bound. |
| 6 | `Soundness.Runtime.stopped_failure_cover` | [`Soundness.StoppedCosts`](lfzk-v2/LfzkV2/Current/Soundness/StoppedCosts.lean) | Pointwise cover outside the hash exception: first transparent escape or retained cost at least one (`stopped_failure_indicator` states it as $\mathbf 1_F\le\mathbf 1_X+\mathbf 1_E+C$). |
| 7 | `Soundness.Runtime.conditioned_cost_mean_le` | [`Soundness.StoppedCosts`](lfzk-v2/LfzkV2/Current/Soundness/StoppedCosts.lean) | The retained Polygero and auxiliary hash cost has mean at most the opaque allowance per opaque query. |
| 8 | `Soundness.Recovery.accepted_recovery_or_hash` | [`Soundness.Recovery`](lfzk-v2/LfzkV2/Current/Soundness/Recovery.lean) | An accepted run recovers the ordered path and opened columns, or pays a hash charge, or lies in the hash exception. |
| 9 | `Soundness.Runtime.accepted_cover` | [`Soundness.Transport`](lfzk-v2/LfzkV2/Current/Soundness/Transport.lean) | On the recovered path, extraction failure triggers one local charge (`Soundness.LocalCharges.decoded_cover`). |
| 10 | `Soundness.LocalCharges.prefixCharge_eq_runtime` | [`Soundness.LocalCharges`](lfzk-v2/LfzkV2/Current/Soundness/LocalCharges.lean) | Local charges at the original commitment cut read only the strict query prefix ([`Protocol.PrefixState`](lfzk-v2/LfzkV2/Current/Protocol/PrefixState.lean)); `single_mean` and `pair_mean` fit the role budgets. |
| 11 | `Survival.QueryStep.step_le` | [`Survival`](survival/README.md) | Generic chronological survival and stopped-search accounting, with no V1 or V2 dependencies. |

The modules `Soundness.Runtime`, `Soundness.Transport` and
`Soundness.StoppedCosts` share the namespace `LfzkV2.Current.Soundness.Runtime`.

The composition takes typed setup, sampler and adversary records. Shared
[`Protocol.Setup`](lfzk-v2/LfzkV2/Current/Protocol/Setup.lean) owns public runtime
data. [`Protocol.ExecutionSampler`](lfzk-v2/LfzkV2/Current/Protocol/ExecutionSampler.lean)
owns the executable callback; [`Protocol.Sampling`](lfzk-v2/LfzkV2/Current/Protocol/Sampling.lean)
adds role factors and the soundness balance law. Privacy and conditional
completeness do not import that latter module.
[`Protocol.Execution`](lfzk-v2/LfzkV2/Current/Protocol/Execution.lean) owns the
original/verifier trace observation and the original-query-bounded adversary.
Soundness setup adds structural layout, framing and resource constraints;
failure coverage and stopped-cost estimates are proved by the composition.

Shared runtime helpers have one owner: `RuntimeVerifier` contains the public
configuration and response codecs; `RuntimeSource` constructs the selected
witness source and its sampling laws; `RuntimeShape` relates generated circuits
to their public schedule. `CertifiedProfile` owns the certified parameter
budget; `RoleBudgets` combines the disjoint application and backend allowances.
Public oracle-dependent setup and its finite family live together in
`Mdoc.PublicSetup`. For frontend privacy, `FrontendRoleWrites` owns role/write
correspondence and `FrontendScheduleLength` owns query-prefix length facts.
Callers use these owning namespaces directly. The source and declaration
audits reject retired implementation paths and compatibility exports.

The original-query collision allowance is `Q(Q-1)/(2*2^256)`. Missing
transcript nodes, an unqueried final seal and a fresh hit on one indexed
Merkle path account for the remaining hash correction. Verifier replay
does not enlarge the adversary's query budget. Transparent application/opening tests use chronological survival. Opaque
Polygero and auxiliary hash costs spend disjoint slots of the stopped original
query budget. Sampler residuals are averaged before the raw hash bound.

The theorem assumes a classical ideal SHA oracle and the approved ideal
joint role-block sampling law. Requested coordinates are uniform jointly,
with the specified nonzero scalars and openings without replacement.
Rejected sampler bytes are outside the requested analysis. Trusted fields,
canonical scalar codecs, trusted application circuits and static public
resource bounds are explicit model inputs. Rust correspondence is established
through source review and tests; machine-level refinement and extractor
running-time bounds remain open. The endpoint's axiom tests report only
`propext`, `Classical.choice` and `Quot.sound`.

## Zero knowledge

[`Mdoc.ZeroKnowledge.statClose`](lfzk-v2/LfzkV2/Current/Mdoc/ZeroKnowledge.lean)
proves statistical zero knowledge for the complete numbered-strand mdoc
runtime model, with public setup computed from the same SHA oracle used by
the proof and observer. For every bounded classical observer and every
observable event `E`,

$$
\left|\Pr[\mathrm{real\ view}\in E]-\Pr[\mathrm{simulated\ view}\in E]\right|
\le \frac{Q_{\mathrm{pre}}+Q_{\mathrm{post}}}{2^{256}}.
$$

`Qpre` and `Qpost` bound the observer's raw calls before and after the proof,
including repetitions. The view retains both query/answer traces, arbitrary
private context, the adaptive public request, the canonical proof or failure,
and the final seal. The simulator has no witness argument. Witness validity
is required only for contexts reached by the prior observer, using setup
derived from that same oracle. This validity, the separate static hash
noninterference premise below, and the stated basis/generator checks derive
backend truth; no execution or simulation certificate is assumed.

The proof separates the three complete-view experiments:

$$
\mathrm{Real}_w \approx_{(Q_{\mathrm{pre}}+Q_{\mathrm{post}})/2^{256}}
\mathrm{Ghost}_w \equiv \mathrm{Sim}.
$$

Independent leaf labels replace salted leaf hashes in the ghost experiment.
[`StrandCanonicalExactSimulation.ghost_sameDistribution`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/StrandCanonicalExactSimulation.lean)
proves the exact second step using one joint frontend/backend coin bijection.
[`StrandCanonicalCommitmentHiding.commitment_hiding`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/StrandCanonicalCommitmentHiding.lean)
proves the statistical first step. Honest execution lives separately in
[`StrandCanonicalExecution`](lfzk-v2/LfzkV2/Current/ZeroKnowledge/StrandCanonicalExecution.lean),
so completeness does not import the privacy assembly.

Only disclosed leaf answers are installed;
a prior-query conflict retains the original oracle and produces failure.
Strand nodes, PRF blocks and the final seal are ordinary oracle evaluations.
There is no digest-collision exception or second statistical hiding loss.

A finite all-branch support is derived for setup, protocol, and both observers.
Pointwise equalities prove that outside answers cannot affect either complete
view. Public identifiers need not be independent: their actual hash evaluations
are included, and setup is preserved while the leaf coordinates vary. No
finite type of all byte strings, finite private-state type, or caller-supplied
support certificate is assumed.

[`Mdoc.VerifierPrivacy.acceptance_probability`](lfzk-v2/LfzkV2/Current/Mdoc/VerifierPrivacy.lean)
compares the actual runtime verifier's acceptance probabilities within the same
bound. The verifier observer is proved equal to the indexed verifier, including
sampler-failure rejection, tuple authentication and the final seal. Rejection
and abort outcomes are retained; the theorem does not assume an always-accepting
simulator.

[`statClose_at_query_budget`](lfzk-v2/LfzkV2/Current/Mdoc/ZeroKnowledge.lean)
checks that `Qpre + Qpost <= 2^128` gives ideal-model error at most `2^-128`.
When verification is included as a later observer, its raw calls count in
`Qpost`. All new endpoint axiom checks permit only `propext`, `Classical.choice`
and `Quot.sound`.

[`Mdoc.Completeness.rawReal_some_accepts`](lfzk-v2/LfzkV2/Current/Mdoc/Completeness.lean)
proves that every proof returned by the actual honest experiment passes the
runtime verifier. It derives parsing, backend truth, original-column
authentication and final sealing from ordinary witness truth and execution.
This is conditional on an actual successful output; sampler aborts remain
possible outcomes of the partial-reader model.

[`Mdoc.Runtime`](lfzk-v2/LfzkV2/Current/Mdoc/Runtime.lean) supplies the same
typed protocol setup to soundness, privacy and honest execution. The
oracle-selected privacy setup is proved equal to that concrete setup.
Privacy and conditional completeness use `Protocol.ExecutionSampler`, which
contains only the executable callback; sampler balance is required separately
by soundness. `Protocol.Execution.PublicView` names the proof, observer result
and before/after traces without exposing private prover execution.

These are ideal-oracle bounds. No numerical SHA-256-to-random-oracle
comparison is proved; the trusted circuit, field, representation and sampling
premises remain explicit.

## Assumptions and remaining correspondence obligations

These are the premises and limits of the current mathematical results. A
successful kernel check establishes the stated implications; it does not
establish that a cryptographic implementation satisfies their premises.

- **Classical ideal oracle and ideal sampling.** One SHA random oracle has
  independent uniform 256-bit answers at distinct byte inputs and consistent
  repeated answers. Canonical domain separation and the oracle-coordinate
  split are proved. Requested role blocks have the approved joint uniform
  law, including nonzero coordinates and sampling without replacement.
  Rejected bytes are outside the requested analysis. Finite-decoder balance
  is explicit in the conditional sampler lemmas. The current soundness
  and numbered-strand privacy endpoints use this single-SHA model. The
  numbered-strand privacy coupling preserves the supplied physical readers,
  including their failure branches; it does not need a separate uniformity
  hypothesis for field challenges. Concrete SHA-256 distinguishing bounds
  and quantum-oracle security remain outside these results.
- **Fresh private randomness for privacy.** Prover masks, pads, commitment nonces and
  the other private coins are independent and uniform. The normal Rust mdoc
  entry point obtains randomness from the operating system. APIs accepting
  a caller-supplied generator require the same randomness property. Merkle
  nonces have 256 bits; they are not assumed collision-free.
- **Fields and representations.** The modeled fields satisfy their field
  laws; bases and scalar representations have their declared cardinality,
  canonical encoding and injectivity properties. The ZK specialization
  explicitly requires binary basis coordinate zero equal to one and a
  successful primitive-generator check.
  Rust limb arithmetic, finite-machine operations and compiler correctness
  are source-correspondence obligations, not additional Lean theorems.
- **Trusted application circuits and archives.** Extraction returns a
  witness satisfying the supplied circuits, not an independently formalized
  ISO mdoc/CBOR specification. Privacy requires signature satisfaction and
  ordinary hash-witness satisfaction, `MdocWitness.HashValid`, at reached
  requests. The static `MdocWitness.ReadDisjoint` certificate syntactically excludes ordinary
  reads of reserved inputs and generated adapter wires, including assertions
  and carried outputs. Lean derives `MdocWitness.HashNoninterference` from
  this certificate, then composes extraction with request readback and ordinary
  hash validity. A satisfying assignment alone does not prove separation. The Rust compiler
  appends the 256 mask and 20 OTP inputs after compiling the application;
  tests reject hash gates or assertions that read this suffix in any of the
  four compiled circuit shapes. Adapter parameters instantiate a separate
  circuit. There is no mask range assertion: `Handoff.product_handoff` handles
  arbitrary mask bits through their residue modulo the prime. These safeguards do
  not replace the explicit Lean circuit-correspondence premise. Rust's normal
  `for_spec` loader recomputes each segmented circuit ID, checks it against
  the archive entry, and checks the combined ID against the trusted spec.
  Trust therefore includes the circuits selected by the spec and their
  application semantics; payload IDs are verified at load time.
- **Public setup and resource bounds.** Trusted sparse topology, canonical
  scalar codecs, capacity/address/serialization bounds and the concrete
  hash-depth restriction are explicit. Current parameter certificates,
  sampler projections, advice decoding, generated adapter equations,
  authenticated row layouts and failure coverage are constructed and
  proved; no caller-supplied execution or soundness certificate replaces
  those proofs.
- **Adversary and witness scope.** The adversary is classical and makes
  finitely many calls within the stated budgets; extraction counts distinct
  original raw SHA inputs. Privacy permits arbitrary retained private context
  and adaptive public requests. The witness policy is a function of the full
  context retained by the prior observer, so two contexts with the same public
  request may select different witnesses. The numbered-strand theorem requires
  valid witnesses only for contexts actually reached under setup computed from
  the same oracle; unreachable policy branches impose no validity obligation.
  Witness selection is fixed at that context before proof generation; the
  simulator remains witness-free.
- **Efficiency and implementation.** Extraction uses mathematical finite
  search; no polynomial-time extractor bound is proved. The explicit public
  simulator has no witness argument, but its running time is not formally
  bounded. Rust correspondence is reviewed and tested, rather than a
  mechanized refinement. A complete Rust-to-Lean verifier replay vector remains
  absent. The separate honest-acceptance theorem covers every successfully
  returned proof, including indexed authentication and the final seal. No timing,
  memory-observation or other implementation side-channel theorem is claimed.

## Component libraries and V1

The [recursive Polygero development](polygero/README.md) preserves its
paper-facing public-coin extraction and false-statement soundness results,
including the certified failure bound `1 - product(1 - epsilon_i)`. The
protected declarations and their contracts are unchanged.

The current V2 verifier uses the [sumcheck](sumcheck-v2/README.md),
[witness-selection](witness-selection/README.md),
[dual-packing](dual-packing/README.md), [Polygero](polygero/README.md) and
[numbered-transcript](transcript-v2/README.md) libraries. Their component
algebra, completeness, masking, query-accounting and sampling results remain
available. Shared helpers keep their existing namespaces; obsolete V2
implementation endpoints are no longer public or registered as current tests.

The extant V1 runtime retains its checked 116-bit extraction and false-statement
soundness bounds. [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) checks the
signature and SHA geometries for one through four attributes. The
[V1 README](lfzk-v1/README.md) states their premises. V1's generic statistical
couplings remain shared dependencies of current V2 privacy.

The [Ligero development](ligero/README.md) contains Reed–Solomon distance,
agreement/list bounds, Delsarte/Hahn certificates, response-assisted extraction,
and Merkle/query bookkeeping. The [EC/ECDSA development](circuits) and both
sumcheck libraries remain available. The V1 security certificates use
[Sumcheck V1](sumcheck-v1/SumcheckV1/README.md); the current V2 construction uses
[Sumcheck V2](sumcheck-v2/README.md).

The default build includes the exact [runtime Hahn certificates](parameters/hahn/RuntimeHahn/APITest.lean)
and the [production joint mdoc profile](parameters/polygero/MdocJointProfile.lean).
The latter re-exports the active `(k,s,n,t) = (349,12,2443,84)` certificate
with both witness-selection list bounds and the joint active-family bound.
The Rust parameter tool checks this profile's joint budget separately from
its universal tuning catalog. Its Lean check binds the manifest's geometry,
cutoffs and list caps to this certificate.

The retained numerical certificates cover V1, the live V2 parameter catalog
and the Polygero paper's benchmark table. Independent kernel identities share
bounded source chunks, avoiding an import and compiler startup for each small
degree. Each chunk checks its identities serially; independent chunks build
in parallel. The generator reproduces this layout.

The default build also includes the
[Polygero parameter certificates](parameters/polygero). These use checked
integer identities and proved interpolation, without a native-evaluation axiom.
The package uses Lean 4.31.0 and the compatible Mathlib checkout at
`../../mathlib4`, relative to `formal/`.

## Bounded soundness checks

`python3 scripts/check_soundness.py` checks the survival library and the current
API aggregate, including the existing zero-knowledge tests. It checks local
dependencies sequentially through Lake, with a 180-second deadline for each
invocation. Lake workers use two Lean threads and a 4,096 MiB Lean memory cap;
proof heartbeat limits are unchanged. Logs and timing JSON are written to
`.lake/soundness-check/`. A focused check is
`python3 scripts/check_soundness.py LfzkV2.Current.Mdoc.Soundness`.

Check import boundaries without building with
`python3 scripts/check_soundness.py --imports-only`.
For a full rebuild with bounded workers, use:

```sh
lake env python3 scripts/rebuild_lean.py --jobs 2 --threads 2 --memory-mib 4096 --module-timeout 60
```

This full-source command includes retained modules outside the default import
closures and honors each library's declared compiler options, including V1's
explicit implicit-variable compatibility settings. The declaration audit
imports the default component roots, including survival and circuit libraries;
it checks declarations and their transitive axiom dependencies. The source
audit also requires every current test to be directly imported by its aggregate.

The rebuild writes per-module times and peak memory to its report under
`.lake/`.
