# Formal security claims and audit

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
| Joint-commitment V2 authenticated extraction, all budgets | [`Joint.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Joint/RawRuntimeExtraction.lean) | `(1+N+tA)/2^116`, for `8943498`; one tree, shared queries, exact finite bound. |
| Linear-terminal V2 authenticated extraction, all budgets | [`Linear.Runtime.RawRuntimeExtraction.extraction_116`](lfzk-v2/LfzkV2/Linear/Runtime/RawRuntimeExtraction.lean) | `(1+N+tA)/2^116`, for snapshot `21cb029`; exact finite bound also proved. |
| Retained product-checked V2 extraction, all budgets | [`Packed.RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/Packed/RawRuntimeExtraction.lean) | `(1+N+tA)/2^117`, under the model premises below. |
| Packed V2 actual compiler instances | [`Packed.Compiled.side`, `Packed.Direct.side`](lfzk-v2/LfzkV2/Packed/CompiledFS.lean), [`ProfiledSide`](lfzk-v2/LfzkV2/Packed/ProfiledSide.lean) | Actual row construction proves the frontend transfer; the profile chooses its candidate bound before that transfer and counting proof. |
| Earlier unpacked V2 authenticated composition | [`RawRuntimeExtraction.extraction_117`](lfzk-v2/LfzkV2/RawRuntimeExtraction.lean) | Retained separate model, with earlier hash geometry and frontend budgets. Its numbered-leaf and annotated-proof variants are not needed by the packed endpoint. |
| Retained standalone Polygero profiles | [`Profile.fs_extraction_failure_127`](parameters/polygero/PolygeroRustHahn.lean) | `(N+1)/2^127`, including satisfiable transcript-dependent statements, in the ideal-binding, uniform-sampler model. Frontend, packing, MAC, and Merkle costs are excluded from this component result. |
| V1 combined extraction and false-statement soundness, all four v7 hash profiles | [`LfzkV1.FlatV7All`](lfzk-v1/LfzkV1/FlatV7All.lean) | `(1+N+tA)/2^116`, under V1's documented circuit, sampler, transcript, and MAC-key coherence premises. |
| V2 privacy components | [`PolygeroZk`](lfzk-v2/LfzkV2/PolygeroZk.lean), [`BackendEncoding`](lfzk-v2/LfzkV2/BackendEncoding.lean), [`Mac`](lfzk-v2/LfzkV2/Mac.lean) | Backend response/opening simulation and affine-tag uniformity. A complete joint frontend/backend/Merkle zero-knowledge theorem is not established. |
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

The runtime's [`polygero/src/hash.rs`](../rust/runtime/polygero/src/hash.rs)
prefixes leaves with `polygero/root/original-leaf/v1` and internal nodes
with `polygero/root/node/v1`. Each leaf includes the context, its column
index as a little-endian `u64`, the salt, and canonical column bytes.
[`verifier.rs`](../rust/runtime/polygero/src/verifier.rs) hashes each opened
column with its sampled index before verifying the Merkle paths;
[`transcript.rs`](../rust/runtime/polygero/src/transcript.rs) samples
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

V2 joint-view zero knowledge still needs the frontend's causal transmission
and commitment-dependent pads combined with the backend simulator and
Merkle-hiding/oracle-programming hybrids. The documentation makes no full
V2 privacy claim.

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
imported declaration owned by the V1/V2, sumcheck, dual-packing, BCS, Merkle, Polygero,
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
