import Lfzk.NizkGrinding
import Bcs.SchemeCompiler

/-!
# The compiled Longfellow verifier, concretely

`Lfzk.CertifiedV1.Row.fs_ratio_le_bound` and `v8Hash_fs_ratio_le` bound
`Pr[CompiledAccepts K A codec … ∧ Fails]` for an **abstract** compiled verifier `K` and abstract
challenge and query maps `challengeOf`, `queryOf`.  Their hypothesis `hright` is what connects that
abstract verifier to the round-by-round LayerStep.  This file fixes the verifier and proves `hright` for
it.

## The verifier

`Accepts` is the conjunction of three checks on one proof, at one hash tape and one challenge tape:

1. **the field rounds** (`FieldPass`): the Longfellow LayerStep's transitions, run on the proof's messages
   at the Fiat–Shamir-recomputed challenges, are still `running` after the input binding.  The
   transitions are `RbrLongfellow`'s (`initStep`, `roundStep`, and the closing step that
   `combineStep` performs), here read from a fixed verifier `Code` with no honest-value data in it;
2. **the Merkle opening** and 3. **Ligero V1's policy on the opened columns**, both inside
   `Bcs.CompiledAccepts` at `v1K`, `Bcs.schemeVerifierCompiler` for `Ligero.V1.scheme` at the
   row's Reed–Solomon code.  Its
   challenge and query are the verifier's decoders applied to the recomputed answers at the two
   Ligero slots (`challengeOf`, `queryOf`).

The verifier's code (`Code`) is fixed: it reads the proof's messages, the earlier raw challenges, and
nothing about the commitment.  LayerStep's analysis data, `Ffam pre` and `MD pre`, may vary with the
commitment, and `Matches` says their computational fields are the code's.

## `hright`, for this verifier

`hright_v1` proves `Row.fs_ratio_le_bound`'s `hright` at
`K := guarded (v1K …)`, `statement := guardedStatement … = (stmt pre, FieldPass …)`, the decoded recomputed
challenge and query, and `lig pre := extractedInstance … pre`, the V1 instance whose prover commits
the **Merkle-extracted** matrix (`Bcs.extractedOracle`) and answers with the adversary's response.
The four pieces `hright` used to bundle:

| piece of `hright` | here |
|---|---|
| 1. the verifier performs LayerStep's checks | **theorem**, given `Matches` (`stepsOf_withMsgs_eq`, `layerStepAccepts_iff`) |
| 2. its challenges are the decoded recomputed answers | **definition** (`challengeOf`, `queryOf`) |
| 3. its Ligero check is V1's policy at the extracted columns | **theorem** (`Bcs.protocol_accepts_of_compiled`, `mem_accepting_extracted`) |
| 4. LayerStep reads the proof's messages | **definition** (`FieldPass` is read at `msgOf (fsProof …)`) |

`guarded` is a formal device only: it puts the field verdict in the statement slot of a
`Bcs.Compiler`, so that `Row.fs_ratio_le_bound`'s event `CompiledAccepts K …` *is* `Accepts`
(`accepts_iff_guarded`).  The headline theorems are stated about `Accepts`.

## What is still a hypothesis

`row_fs_ratio_le_v1` lists them; `hright` is not among them.  Besides `hr : 0 < openings` (the
compiler opens something; `decide` at the rows), `Matches` is the one new premise.  It is an
equality of data: LayerStep data's initial state, decoders, closing maps and round polynomials
are the verifier's.  It is satisfiable whenever those computational fields do not vary with the
commitment (`Code.ofData`, `matches_ofData`).  Claim 3 needed the Ligero oracle to be the
Merkle-extracted matrix.  That is now a definition (`extractedInstance`), so no extraction hypothesis
remains for it.  Whether the commitment's Ligero statement is false when extraction fails is
`hfalse`, as before.  Joint satisfiability of all the premises is still not witnessed in Lean.

## Which verifier this is

The field rounds are checked **in the clear**: `roundStep` runs `check_round_c`, which models the
non-zero-knowledge `VerifierLayers` round check (`verifier_layers.h:L84-L98`) on the transmitted
round polynomial.  The Ligero statement `stmt pre` is fixed per commitment.  So `Accepts` is a
non-ZK-path sumcheck verifier composed with a Merkle-compiled Ligero V1 check.  It is **not** the
deployed zero-knowledge verifier, which differs in two places:

* it performs no round check on cleartext polynomials.  The round polynomials are padded, and
  `ConstraintBuilder::next` substitutes `p(1) := claim − p(0)` (`zk_common.h:L336-L337`), so
  sum-consistency holds by construction (`Lfzk.Builder`);
* its Ligero statement is a function of the transcript: `ConstraintBuilder` turns the run's
  challenges and padded messages into the linear rows (`zk_common.h:L250-L400`).

A reading of LayerStep, not a Lean theorem: `Wrong` at `.challenged x` is `LigDoomed x`, and
`ligeroChallengeStep` sends every running state to `.challenged`.  So at a commitment where `hfalse`
applies, the Ligero slots are charged whatever the field state was.  The field rounds' budgets enter
the bound, but soundness at a failing commitment comes from `hfalse` and Ligero's round-by-round
theorem.

## The residual refinement claim (README gap 1)

What would make `v8Hash_compiled_fs_ratio_le` a statement about the deployed verifier.  None of it
is proved.  There exist Lean data `V`, `msgOf`, `stmt`, `codec`, `dec`, `dom`, and for every
deployed prover `P*` a Lean adversary `(A, adv)`, such that, with the deployed hash read as two
lazily sampled random oracles (the hash tape and the challenge tape),

```text
deployed verifier accepts P*'s proof   ⟹   Accepts (v1K …) V A codec adv dflt ctxOf msgOf stmt ω
```

conjunct by conjunct:

* **R1, Merkle.**  Deployed Merkle verification of the opened columns against the root implies
  `claim.I = query.coordinates ∧ MH.Accepts …`, with a leaf being a `Col` and `codec` injective per
  role (`RoleDecoders`);
* **R2, Ligero.**  The deployed Ligero check implies `SchemeVerifier.Accepts (code) V1.scheme
  (stmt pre) challenge response query opening` at the Reed–Solomon code over `dom`, with the
  deployed response read as a `LigeroFamily.Response` (the type carries the whole codeword row; the
  protocol transmits less);
* **R3, field rounds.**  The deployed sumcheck checks imply `FieldPass V (msgOf out) chals`;
* **R4, challenges.**  Round `k`'s deployed challenge is `V.decode…` of the oracle at
  `hashPoint (ctxOf aux) msgOf out k (answers < k)`.  This needs domain separation between Merkle
  and Fiat–Shamir hashing.  It also needs the reduction from a deployed hash query, whose input
  carries messages only, to queries at `Point`s, which carry the raw earlier answers.  `N` in the
  bound counts `Point` queries.  A naive simulation recomputes the earlier answers, which costs up
  to `L = 595` `Point` queries per deployed query.  Neither that translation nor a sharper one is
  proved;
* **R5, Ligero statement.**  The deployed statement equals `stmt pre`, a function of the commitment
  alone;
* **R6, context.**  `ctxOf (A.auxOf pre)` is what the deployed transcript hashes first (the root),
  which holds for any adversary that stores its root in `Aux`.

**R3 and R5 fail for the deployed zero-knowledge verifier**, for the two reasons in the previous
section.  The deployed ZK verifier is not an instance of `Accepts` as LayerStep stands, and the
refinement it needs is a different LayerStep: one whose Ligero statement, and so whose Ligero doom, reads
the transcript.  R1, R2, R4 and R6 are transliteration debt of gap 1's kind.

## Modelling restrictions, unchanged

`Lfzk.NizkGrinding`'s: one commitment, no Merkle queries during the search, hash inputs carry the
raw earlier answers, and the Ligero statement `stmt pre` is fixed per commitment.  The context
`ctxOf aux` hashed into every challenge is the adversary's.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledLongfellow

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle RbrLongfellow Lfzk.NizkGrinding
open scoped Classical

/-! ## 1. A compiler with a guard in its statement -/

section Guard

variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {M : Type} {n : ℕ}

/-- **`K` with a Boolean guard.**  The statement is `K`'s statement and a bit, and the verifier
accepts iff the bit is set and `K`'s verifier accepts.  Commitment, leaves and opened set are `K`'s,
so locality is `K`'s. -/
def guarded (K : Compiler Statement Oracle Challenge Response Query Opening M n) :
    Compiler (Statement × Bool) Oracle Challenge Response Query Opening M n where
  protocol :=
    { language := fun s => K.protocol.language s.1
      openOracle := K.protocol.openOracle
      verify := fun s challenge response query opening =>
        s.2 && K.protocol.verify s.1 challenge response query opening }
  columns := K.columns
  indices := K.indices
  indices_nonempty := K.indices_nonempty
  open_congr := K.open_congr

variable {Enc D Salt Aux Aux' : Type} {commitFuel respondFuel revealFuel T : ℕ}

/-- The guarded compiled verifier is the guard and `K`'s compiled verifier. -/
theorem compiledAccepts_guarded [Inhabited D] [DecidableEq Enc]
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (codec : Codec Salt M D Enc) (s : Statement) (b : Bool) (challenge : Challenge)
    (query : Query) (answers : Fin T → D) :
    CompiledAccepts (guarded K) A codec (s, b) challenge query answers ↔
      b = true ∧ CompiledAccepts K A codec s challenge query answers := by
  unfold CompiledAccepts Compiler.Accepts
  simp only [guarded, Compiler.oracleOfClaim, Bool.and_eq_true]
  tauto

end Guard

/-! ## 2. The verifier's field computation -/

section Code

variable {C F X Q Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {logw logc : ℕ}

/--
**The verifier's own data for the field rounds.**  Nothing in it is an honest value: the initial
state, the closing map and next layer a message determines, the round polynomial a message
transmits, and the four coin decoders.  Each may read the earlier raw challenges, as `MsgData` may.
-/
structure Code (C F X Q Msg : Type) (logw logc : ℕ) where
  /-- Layer 0's incoming state (`verifier_layers.h:L70`: claims of zero). -/
  st0 : LayerState logw logc F
  /-- Close a layer: check its identity against the message and form the next state, or reject. -/
  close : ∀ m : ℕ, (Fin m → C) → Msg →
    ℕ → LayerState logw logc F → F → F → List F → F → Option (LayerState logw logc F)
  /-- Which layer LayerStep moves to. -/
  next : ∀ m : ℕ, (Fin m → C) → Msg → ℕ → ℕ
  /-- The round polynomial a message transmits. -/
  poly : ∀ m : ℕ, (Fin m → C) → Msg →
    ℕ → LayerState logw logc F → F → F → List F → Sumcheck.RoundPoly F 2
  /-- `begin_layer`'s coin decoder. -/
  decodePair : C → F × F
  /-- The field-element decoder. -/
  decodeF : C → F
  /-- Ligero's linear-combination decoder. -/
  decodeChal : C → X
  /-- Ligero's query decoder. -/
  decodeQuery : C → Q

/-- **Close, then combine**, from the closing map alone: `combineStep` with its boundary's two
computational fields and nothing else. -/
def closeStep {X : Type}
    (close : ℕ → LayerState logw logc F → F → F → List F → F → Option (LayerState logw logc F))
    (next : ℕ → ℕ) (decode : C → F) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .start => .failed
  | .challenged _ => .failed
  | .accepted => .failed
  | .failed => .failed
  | .running ws =>
      match close ws.layer ws.st ws.beta0 ws.alpha ws.bound ws.claim with
      | none => .failed
      | some st' =>
          .running { layer := next ws.layer
                     beta0 := ws.beta0
                     st := st'
                     alpha := decode c
                     bound := []
                     claim := st'.claim0 + decode c * st'.claim1 }

omit [Fintype C] [Fintype F] [DecidableEq F] in
/-- `combineStep` reads its boundary's `close` and `next` and nothing else. -/
theorem combineStep_eq_closeStep [SumcheckInterp F] {Cand X : Type}
    {H : Honest F Cand logw logc} (B : Boundary H) (decode : C → F) (c : C)
    (s : RbrLayerStep.WState logw logc F X) :
    combineStep B decode c s = closeStep B.close B.next decode c s := by
  cases s <;> rfl

variable [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]

/-- **The verifier's transitions** on a proof's messages `ms`, with query test `acc`.  The same
dispatch as `RbrLongfellow.lfSteps`, read from the code. -/
noncomputable def Code.steps {nl : ℕ} {w : ℕ → ℕ} (V : Code C F X Q Msg logw logc)
    (ms : ℕ → Msg) (acc : ∀ m : ℕ, (Fin m → C) → X → Finset Q) :
    RbrLayerStep.Steps C F X logw logc nl w where
  pair ly m pref c s :=
    if ly.val = 0 then initStep V.st0 V.decodePair c s
    else closeStep (V.close m pref (ms m)) (V.next m pref (ms m)) V.decodeF c s
  round _ _ m pref c s := roundStep (V.poly m pref (ms m)) V.decodeF c s
  inputBind m pref c s := closeStep (V.close m pref (ms m)) (V.next m pref (ms m)) V.decodeF c s
  ligeroChallenge _ _ c s := ligeroChallengeStep V.decodeChal c s
  ligeroQuery m pref c s := ligeroQueryStep V.decodeQuery (acc m pref) c s

/--
**LayerStep data describes this verifier.**  The field half's initial state and decoders are the
code's, and the message data's closing maps, next layers and round polynomials are the code's.
Everything else in `FD` and `MD` — the circuit, the honest values, `Boundary.rel` and
`Boundary.sound` — is analysis, and is not constrained.
-/
structure Matches {Cand Witness : Type} {nc nv : ℕ} {H : Honest F Cand logw logc}
    {Sat : Cand → Prop} (V : Code C F X Q Msg logw logc)
    (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) : Prop where
  st0 : FD.st0 = V.st0
  decodePair : FD.decodePair = V.decodePair
  decodeF : FD.decodeF = V.decodeF
  decodeChal : FD.decodeChal = V.decodeChal
  decodeQuery : FD.decodeQuery = V.decodeQuery
  close : ∀ (m : ℕ) (pref : Fin m → C) (msg : Msg), (MD.bnd m pref msg).close = V.close m pref msg
  next : ∀ (m : ℕ) (pref : Fin m → C) (msg : Msg), (MD.bnd m pref msg).next = V.next m pref msg
  poly : MD.poly = V.poly

/-- **The code a LayerStep datum's computational fields define.**  With `matches_ofData`, `Matches` costs
nothing beyond LayerStep data's computational fields being the same at every commitment. -/
def Code.ofData {Cand Witness : Type} {nc nv : ℕ} {H : Honest F Cand logw logc}
    {Sat : Cand → Prop} (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) : Code C F X Q Msg logw logc where
  st0 := FD.st0
  close m pref msg := (MD.bnd m pref msg).close
  next m pref msg := (MD.bnd m pref msg).next
  poly := MD.poly
  decodePair := FD.decodePair
  decodeF := FD.decodeF
  decodeChal := FD.decodeChal
  decodeQuery := FD.decodeQuery

/-- `Matches` is satisfiable: LayerStep data match the code they define. -/
theorem matches_ofData {Cand Witness : Type} {nc nv : ℕ} {H : Honest F Cand logw logc}
    {Sat : Cand → Prop} (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) : Matches (Code.ofData FD MD) FD MD :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl⟩

/-- **LayerStep's transitions at a proof are the verifier's.** -/
theorem stepsOf_withMsgs_eq {nl : ℕ} {w : ℕ → ℕ} {Cand Witness : Type} {nc nv : ℕ}
    {H : Honest F Cand logw logc} {Sat : Cand → Prop} {V : Code C F X Q Msg logw logc}
    {FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat} {MD : MsgData C Msg H}
    (hm : Matches V FD MD) (ms : ℕ → Msg) (acc : ∀ m : ℕ, (Fin m → C) → X → Finset Q) :
    RbrSplit.stepsOf (nl := nl) (w := w) (withMsgs FD MD ms) acc = V.steps ms acc := by
  simp only [RbrSplit.stepsOf, lfSteps, Code.steps, withMsgs]
  rw [hm.poly, hm.decodeF, hm.decodeChal, hm.decodeQuery, hm.st0, hm.decodePair]
  congr 1
  · funext ly m pref c s
    rw [combineStep_eq_closeStep, hm.close, hm.next]
  · funext m pref c s
    rw [combineStep_eq_closeStep, hm.close, hm.next]

end Code

/-! ## 3. Where LayerStep can fail: the field rounds, then the two Ligero slots

The schedule ends `inputBind, ligeroChallenge, ligeroQuery` at slots `b, b + 1, b + 2`,
`b = layerBase w nl` (`Rounds.Role.slot`).  So LayerStep reaches `.accepted` exactly when it is still
`running` after slot `b` — every field check passed — and the drawn query is in the query test at
the drawn challenge (`layerStepAccepts_iff`).  The first part does not read the query test
(`state_acc_congr`), which is what lets `FieldPass` be stated without one.
-/

section Decompose

variable {C F X Q Msg : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}

/-- The Ligero challenge's slot, `layerBase w nl + 1`. -/
abbrev ligIdx : Fin (Rounds.Role.length nl w) :=
  (Rounds.Role.ligeroChallenge : Rounds.Role nl w).index

/-- The Ligero query's slot, `layerBase w nl + 2`. -/
abbrev qryIdx : Fin (Rounds.Role.length nl w) :=
  (Rounds.Role.ligeroQuery : Rounds.Role nl w).index

theorem fieldLen_le : Rounds.Role.layerBase w nl + 1 ≤ Rounds.Role.length nl w := by
  unfold Rounds.Role.length; omega

theorem queryLen_le : Rounds.Role.layerBase w nl + 2 ≤ Rounds.Role.length nl w := by
  unfold Rounds.Role.length; omega

/-- LayerStep the verifier runs, as a claim chain with no candidates. -/
noncomputable abbrev run (steps : RbrLayerStep.Steps C F X logw logc nl w) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) (RbrLayerStep.WState logw logc F X) PUnit :=
  RbrLayerStep.layerStepChain (Cand := PUnit) steps (fun _ _ => False) .start

/--
**The field rounds pass**: after the input binding (slot `layerBase w nl`), LayerStep on the proof's
messages is still `running`.  Every layer pair, sumcheck round and closing check has passed.
-/
def FieldPass (V : Code C F X Q Msg logw logc) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C) : Prop :=
  ∃ ws : RbrLayerStep.LayerStepState logw logc F,
    (run (V.steps (nl := nl) (w := w) ms fun _ _ _ => ∅)).state (Rounds.Role.layerBase w nl + 1)
      (Bcs.trunc tape _ fieldLen_le) = .running ws

omit [Fintype C] in
/-- One more slot of a truncated tape is one more transition. -/
theorem state_trunc_succ {S Cand : Type} {T : ℕ} (ch : Bcs.ClaimChain C T S Cand)
    (tape : Fin T → C) (i : Fin T) :
    ch.state (i.val + 1) (Bcs.trunc tape (i.val + 1) i.isLt)
      = ch.step i (Bcs.trunc tape i.val (le_of_lt i.isLt)) (tape i)
          (ch.state i.val (Bcs.trunc tape i.val (le_of_lt i.isLt))) := by
  rw [Bcs.trunc_succ, Bcs.ClaimChain.state_extend]
  rfl

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [DecidableEq X]
  [Fintype Q] in
/-- LayerStep's step at a role's slot is that role's transition. -/
theorem run_step_index (steps : RbrLayerStep.Steps C F X logw logc nl w) (rl : Rounds.Role nl w)
    (pref : Fin rl.index.val → C) (c : C) (s : RbrLayerStep.WState logw logc F X) :
    (run steps).step rl.index pref c s = RbrLayerStep.stepAt steps rl rl.index.val pref c s := by
  show RbrLayerStep.stepAt steps (Rounds.Role.indexEquiv.symm rl.index) rl.index.val pref c s = _
  rw [indexEquiv_symm_index]

omit [Fintype C] [Fintype F] [DecidableEq X] [Fintype Q] in
/-- **Before the query slot, LayerStep does not read the query test.** -/
theorem state_acc_congr (V : Code C F X Q Msg logw logc) (ms : ℕ → Msg)
    (acc acc' : ∀ m : ℕ, (Fin m → C) → X → Finset Q) (j : ℕ)
    (hj : j ≤ Rounds.Role.layerBase w nl + 2) (p : Fin j → C) :
    (run (V.steps (nl := nl) (w := w) ms acc)).state j p
      = (run (V.steps (nl := nl) (w := w) ms acc')).state j p := by
  refine state_congr_below (run (V.steps (nl := nl) (w := w) ms acc))
    (run (V.steps (nl := nl) (w := w) ms acc')) rfl (Rounds.Role.layerBase w nl + 2)
    (fun i hi => ?_) j hj p
  funext pref c s
  show RbrLayerStep.stepAt (V.steps ms acc) (Rounds.Role.indexEquiv.symm i) i.val pref c s
    = RbrLayerStep.stepAt (V.steps ms acc') (Rounds.Role.indexEquiv.symm i) i.val pref c s
  cases hrole : Rounds.Role.indexEquiv.symm i with
  | ligeroQuery =>
      have hi' := index_indexEquiv_symm (nl := nl) (w := w) i
      rw [hrole] at hi'
      have hv : i.val = Rounds.Role.layerBase w nl + 2 := by rw [← hi']; rfl
      omega
  | layerPair _ => rfl
  | sumcheck _ _ => rfl
  | inputBind => rfl
  | ligeroChallenge => rfl

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [DecidableEq X]
  [Fintype Q] in
/-- The two Ligero transitions accept exactly from a running state, at a query in the test. -/
theorem ligero_accepted_iff (dq : C → Q) (A : X → Finset Q) (dc : C → X) (cq cx : C)
    (s : RbrLayerStep.WState logw logc F X) :
    ligeroQueryStep dq A cq (ligeroChallengeStep dc cx s) = .accepted ↔
      (∃ ws, s = .running ws) ∧ dq cq ∈ A (dc cx) := by
  cases s with
  | running ws =>
      simp only [ligeroChallengeStep, ligeroQueryStep]
      split_ifs with h <;> simp [h]
  | start => simp [ligeroChallengeStep, ligeroQueryStep]
  | challenged _ => simp [ligeroChallengeStep, ligeroQueryStep]
  | accepted => simp [ligeroChallengeStep, ligeroQueryStep]
  | failed => simp [ligeroChallengeStep, ligeroQueryStep]

omit [Fintype C] [Fintype F] [DecidableEq X] [Fintype Q] in
/--
**The verifier's LayerStep accepts iff the field rounds pass and the drawn query passes.**  At the
query slot LayerStep reads the test at the challenge decoded at the Ligero challenge slot.
-/
theorem layerStepAccepts_iff (V : Code C F X Q Msg logw logc) (ms : ℕ → Msg)
    (acc : ∀ m : ℕ, (Fin m → C) → X → Finset Q) (tape : Fin (Rounds.Role.length nl w) → C) :
    RbrSplit.LayerStepAccepts (V.steps (nl := nl) (w := w) ms acc) tape ↔
      FieldPass V ms tape ∧
        V.decodeQuery (tape qryIdx) ∈ acc (Rounds.Role.layerBase w nl + 2)
          (Bcs.trunc tape _ queryLen_le) (V.decodeChal (tape ligIdx)) := by
  set ch := run (V.steps (nl := nl) (w := w) ms acc)
  have h3 : ch.state (Rounds.Role.length nl w) (Bcs.trunc tape _ le_rfl)
      = ligeroQueryStep V.decodeQuery
          (acc (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le)) (tape qryIdx)
          (ch.state (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le)) := by
    have h := state_trunc_succ ch tape qryIdx
    rw [run_step_index] at h
    exact h
  have h2 : ch.state (Rounds.Role.layerBase w nl + 2) (Bcs.trunc tape _ queryLen_le)
      = ligeroChallengeStep V.decodeChal (tape ligIdx)
          (ch.state (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le)) := by
    have h := state_trunc_succ ch tape ligIdx
    rw [run_step_index] at h
    exact h
  have h1 : ch.state (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le)
      = (run (V.steps (nl := nl) (w := w) ms fun _ _ _ => ∅)).state
          (Rounds.Role.layerBase w nl + 1) (Bcs.trunc tape _ fieldLen_le) :=
    state_acc_congr V ms acc _ _ (by omega) _
  show ch.state (Rounds.Role.length nl w) (Bcs.trunc tape _ le_rfl) = .accepted ↔ _
  rw [h3, h2, ligero_accepted_iff, h1]
  rfl

end Decompose

/-! ## 4. The compiled verifier

`Accepts` at any compiler `K` whose challenge and query are LayerStep's `X` and `Q`; the headline
theorems take `K := v1K`, the V1 compiler at the row's Reed–Solomon code.
-/

section Verifier

variable {C F X Q Msg : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}
variable {Ctx Out Aux : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}

/-- **The verifier's Ligero challenge**: the challenge decoder at the recomputed answer of the
Ligero challenge slot. -/
noncomputable def challengeOf (V : Code C F X Q Msg logw logc)
    (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctxOf : Aux → Ctx)
    (msgOf : Out → ℕ → Msg) {T : ℕ} (aux : Aux) (ct : Fin T → C) : X :=
  V.decodeChal (fsChallenges (adv aux) dflt (ctxOf aux) msgOf ct ligIdx)

/-- **The verifier's Ligero query**: the query decoder at the recomputed answer of the query slot. -/
noncomputable def queryOf (V : Code C F X Q Msg logw logc)
    (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctxOf : Aux → Ctx)
    (msgOf : Out → ℕ → Msg) {T : ℕ} (aux : Aux) (ct : Fin T → C) : Q :=
  V.decodeQuery (fsChallenges (adv aux) dflt (ctxOf aux) msgOf ct qryIdx)

variable {Statement Oracle Response : Type} {Opening : Q → Type} {M : Type} {n : ℕ}
variable {Enc D Salt Aux' : Type} [Inhabited D] [DecidableEq Enc]
variable {tlen commitFuel respondFuel revealFuel : ℕ}

/--
**The compiled Longfellow verifier.**  On a hash tape `omega.1` and a challenge tape `omega.2`, with
the Fiat–Shamir search's proof `out = fsProof …` and the recomputed answers `fsChallenges …`:

* LayerStep's field rounds pass on `out`'s messages at the recomputed answers (`FieldPass`), and
* `K`'s compiled verifier accepts — the opened set is the query's, the Merkle opening reconstructs
  the root, and `K`'s IPCP verifier accepts the opened leaves — at the decoded recomputed challenge
  and query (`challengeOf`, `queryOf`), on the statement `stmt omega.1`.
-/
def Accepts (K : Compiler Statement Oracle X Response Q Opening M n)
    (V : Code C F X Q Msg logw logc)
    (A : Adversary Enc D Salt M X Response Q Aux Aux' n commitFuel respondFuel revealFuel)
    (codec : Codec Salt M D Enc) (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg) (stmt : (Fin tlen → D) → Statement) {T : ℕ}
    (omega : (Fin tlen → D) × (Fin T → C)) : Prop :=
  FieldPass V (msgOf (fsProof (adv (A.auxOf omega.1)) dflt (ctxOf (A.auxOf omega.1)) msgOf omega.2))
      (fsChallenges (adv (A.auxOf omega.1)) dflt (ctxOf (A.auxOf omega.1)) msgOf omega.2) ∧
    CompiledAccepts K A codec (stmt omega.1)
      (challengeOf V adv dflt ctxOf msgOf (A.auxOf omega.1) omega.2)
      (queryOf V adv dflt ctxOf msgOf (A.auxOf omega.1) omega.2) omega.1

/-- The statement handed to `guarded K`: the Ligero statement and the field rounds' verdict. -/
noncomputable def guardedStatement (V : Code C F X Q Msg logw logc)
    (A : Adversary Enc D Salt M X Response Q Aux Aux' n commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctxOf : Aux → Ctx)
    (msgOf : Out → ℕ → Msg) (stmt : (Fin tlen → D) → Statement) {T : ℕ}
    (omega : (Fin tlen → D) × (Fin T → C)) : Statement × Bool :=
  (stmt omega.1, decide (FieldPass V
    (msgOf (fsProof (adv (A.auxOf omega.1)) dflt (ctxOf (A.auxOf omega.1)) msgOf omega.2))
    (fsChallenges (adv (A.auxOf omega.1)) dflt (ctxOf (A.auxOf omega.1)) msgOf omega.2)))

omit [Fintype C] [Nonempty C] [Fintype F] [DecidableEq X] [Fintype Q] [Inhabited Msg] in
/-- **`Accepts` is `guarded K`'s compiled verifier**, at the guarded statement. -/
theorem accepts_iff_guarded (K : Compiler Statement Oracle X Response Q Opening M n)
    (V : Code C F X Q Msg logw logc)
    (A : Adversary Enc D Salt M X Response Q Aux Aux' n commitFuel respondFuel revealFuel)
    (codec : Codec Salt M D Enc) (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C)
    (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg) (stmt : (Fin tlen → D) → Statement) {T : ℕ}
    (omega : (Fin tlen → D) × (Fin T → C)) :
    Accepts K V A codec adv dflt ctxOf msgOf stmt omega ↔
      CompiledAccepts (guarded K) A codec (guardedStatement V A adv dflt ctxOf msgOf stmt omega)
        (challengeOf V adv dflt ctxOf msgOf (A.auxOf omega.1) omega.2)
        (queryOf V adv dflt ctxOf msgOf (A.auxOf omega.1) omega.2) omega.1 := by
  rw [guardedStatement, compiledAccepts_guarded, decide_eq_true_iff]
  rfl

end Verifier

/-! ## 5. Ligero V1: the extracted instance, and `hright` -/

section V1

open Lfzk.LigeroV1Rows

variable {C F Equations Msg : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}
variable {row : Row} {nw nq qw : ℕ}

/-- **The V1 compiler at the row's Reed–Solomon code**: `Bcs.schemeVerifierCompiler` at
`Ligero.V1.scheme`.  A leaf is a committed column and the opened set is the query's
coordinates. -/
noncomputable abbrev v1K (h : row.Valid)
    (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings) :=
  Bcs.schemeVerifierCompiler (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) (LigeroV1LayerStep.code h dom hkrow) Ligero.V1.scheme hr

variable {Enc D Salt Aux Aux' : Type} [Inhabited D] [DecidableEq D] [DecidableEq Enc]
  [Inhabited Salt]
variable {tlen commitFuel respondFuel revealFuel : ℕ}

/--
**The V1 instance the compiled verifier is about.**  The statement is `stmt pre`; the prover commits
the matrix **Merkle extraction recovers from the commitment trace** (`Bcs.extractedOracle`, a
function of the hash tape alone) and answers each challenge as the compiled adversary does.
-/
noncomputable def extractedInstance (h : row.Valid)
    (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1) D Enc}
    (dec : RoleDecoders codec)
    (A : Adversary Enc D Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1)
      (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroFamily.Response F row.openings qw row.n 1)
      (LigeroV1LayerStep.Qry row) Aux Aux' row.n commitFuel respondFuel revealFuel)
    (stmt : (Fin tlen → D) → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    (pre : Fin tlen → D) : LigeroV1LayerStep.Instance row F Equations nw nq qw where
  statement := stmt pre
  prover := (v1K h dom hkrow hr).prover (extractedOracle dec (v1K h dom hkrow hr) A pre)
    fun c => A.responseOf c pre

omit [Fintype F] [SumcheckInterp F] [DecidableEq Equations] in
/--
**Claim 3: the compiled Ligero check is V1's policy at the extracted columns.**  Where extraction
explains the opening, a compiled acceptance at `(challenge, query)` puts `query` in LayerStep's V1
query test for the extracted instance at `challenge`.  `Bcs.protocol_accepts_of_compiled`, and the
V1 protocol's verifier is `decide` of the V1 policy.
-/
theorem mem_accepting_extracted (h : row.Valid)
    (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1) D Enc}
    (dec : RoleDecoders codec)
    (A : Adversary Enc D Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1)
      (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroFamily.Response F row.openings qw row.n 1)
      (LigeroV1LayerStep.Qry row) Aux Aux' row.n commitFuel respondFuel revealFuel)
    (stmt : (Fin tlen → D) → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    (pre : Fin tlen → D) (challenge : LigeroV1LayerStep.Chal F Equations nw nq)
    (query : LigeroV1LayerStep.Qry row)
    (hexp : ExtractionExplains codec dec row.n commitFuel (revealFuel + respondFuel) tlen A.commit
      (A.openingStage challenge query) pre)
    (hacc : CompiledAccepts (v1K h dom hkrow hr) A codec (stmt pre) challenge query pre) :
    query ∈ LigeroV1LayerStep.accepting h dom hkrow (extractedInstance h dom hkrow hr dec A stmt pre)
      challenge := by
  have hprot := protocol_accepts_of_compiled dec (v1K h dom hkrow hr) A (stmt pre) challenge query
    pre hexp hacc
  unfold LigeroV1LayerStep.accepting
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, @of_decide_eq_true _ _ hprot⟩

variable {Ctx Out Cand Witness : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
variable {nc nv : ℕ}

omit [Nonempty C] [Inhabited Msg] in
/--
**`hright`, proved for the compiled Longfellow verifier.**

`Row.fs_ratio_le_bound`'s acceptance hypothesis at `K := guarded (v1K …)`, `statement :=
guardedStatement …`, `challengeOf`/`queryOf` the decoded recomputed Ligero rounds, and
`lig pre := extractedInstance … pre`.  From the guarded acceptance: the guard is `FieldPass`, and the
V1 part puts the drawn query in the extracted instance's test (`mem_accepting_extracted`); with the
LayerStep data matching the verifier, these two are LayerStep's acceptance (`stepsOf_withMsgs_eq`,
`layerStepAccepts_iff`).
-/
theorem hright_v1 (h : row.Valid)
    (dom : LigeroFamily.ReedSolomon.Domain F row.openings qw row.n)
    (hkrow : row.openings + qw = row.k) (hr : 0 < row.openings)
    {codec : Codec Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1) D
      Enc}
    (dec : RoleDecoders codec)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroV1LayerStep.Qry row) Msg logw logc)
    (A : Adversary Enc D Salt (LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1)
      (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroFamily.Response F row.openings qw row.n 1)
      (LigeroV1LayerStep.Qry row) Aux Aux' row.n commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C nl w) C Out N) (dflt : C) (ctxOf : Aux → Ctx)
    (msgOf : Out → ℕ → Msg)
    (stmt : (Fin tlen → D) → LigeroFamily.ConstraintSystem F nw nq qw Equations)
    {H : Honest F Cand logw logc} {Sat : Cand → Prop}
    (FD : RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations nw nq) (LigeroV1LayerStep.Qry row) Cand
      Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (hm : Matches V FD MD) (pre : Fin tlen → D)
    (ct : Fin (Rounds.Role.length nl w + N) → C) :
    (CompiledAccepts (guarded (v1K h dom hkrow hr)) A codec
        (guardedStatement V A adv dflt ctxOf msgOf stmt (pre, ct))
        (challengeOf V adv dflt ctxOf msgOf (A.auxOf pre) ct)
        (queryOf V adv dflt ctxOf msgOf (A.auxOf pre) ct) pre ∧
      ExtractionExplains codec dec row.n commitFuel (revealFuel + respondFuel) tlen A.commit
        (A.openingStage (challengeOf V adv dflt ctxOf msgOf (A.auxOf pre) ct)
          (queryOf V adv dflt ctxOf msgOf (A.auxOf pre) ct)) pre) →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := nl) (w := w)
          (withMsgs FD MD (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
          (fun _ _ => LigeroV1LayerStep.accepting h dom hkrow
            (extractedInstance h dom hkrow hr dec A stmt pre)))
        (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct) := by
  rintro ⟨hacc, hexp⟩
  rw [guardedStatement, compiledAccepts_guarded, decide_eq_true_iff] at hacc
  obtain ⟨hfield, hv1⟩ := hacc
  rw [stepsOf_withMsgs_eq hm, layerStepAccepts_iff]
  exact ⟨hfield, mem_accepting_extracted h dom hkrow hr dec A stmt pre _ _ hexp hv1⟩

end V1

/-! ## 6. The certified V1 row, at the compiled verifier -/

/-- A V1 leaf: one committed column. -/
abbrev Col (F : Type) [Field F] (nw nq : ℕ) : Type :=
  LigeroFamily.SchemeColumn F LigeroFamily.NoMask Ligero.V1.Mask nw nq 1

section Row

open Lfzk.CertifiedV1

/--
**A certified V1 row, at the compiled Longfellow verifier, against a grinding Fiat–Shamir adversary.**

```text
Pr[ Accepts (v1K …) V A codec adv dflt ctxOf msgOf stmt  ∧  Fails ]  ≤  R.bound + N · R.fsCoefficient
```

`Accepts` is the conjunction of LayerStep's field checks on the proof's messages at the recomputed
challenges, the Merkle opening check, and V1's policy on the opened columns at the decoded recomputed
challenge and query.  `Lfzk.CertifiedV1.Row.fs_ratio_le_bound` with its `hright` discharged by
`hright_v1`; `challengeOf`, `queryOf`, `statement` and `lig` are no longer parameters.

**Every premise**, and nothing else:

* the protocol instance — `hr : 0 < openings` (the compiler opens something), `|F| = row.fieldSize`
  (`hF`), a Reed–Solomon domain `dom`, the verifier's field code `V`, the Ligero statement per
  commitment `stmt`, the field half of LayerStep `Ffam` with exactly balanced decoders (`hexact`) and
  `RbrLongfellow`'s field premises inside it, the message data `MD`, `|Cand|`, `|D|`, and the Merkle
  fuels `ht₁`, `hT`, `hT1`;
* `hmatch` — LayerStep data's computational fields are `V`'s (`Matches`): an equality of data;
* `hfalse` — at a commitment where extraction fails, `stmt pre` is false (what the V1 theorem
  needs);
* `hfail` — extraction failure means no candidate satisfies the circuit.
-/
theorem row_fs_ratio_le_v1 {R : Row} (h : R.Valid) (hr : 0 < R.params.row.openings)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (stmt : (Fin R.tape → D) →
      LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F R.params.nw R.params.nq)
      (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
      (LigeroV1LayerStep.Qry R.params.row) Aux Aux' R.params.row.n R.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin R.tape → D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (hfalse : ∀ pre : Fin R.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin R.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin R.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin R.tape → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin R.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin R.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin R.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin R.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : R.commitFuel ≤ R.tape)
    (hT : 2 * R.params.row.n + (revealFuel + respondFuel) + R.commitFuel ≤ R.tape)
    (hT1 : 1 ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid h) dom (Row.hkrow h) hr) V A codec adv dflt ctxOf msgOf stmt
          omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin R.tape → D) * (Fintype.card C : ℚ) ^ (R.fsLen N))
      ≤ R.bound + N * R.fsCoefficient := by
  refine le_trans (le_of_eq ?_)
    (Row.fs_ratio_le_bound h dec (guarded (v1K (Row.rowValid h) dom (Row.hkrow h) hr)) A adv dflt
      ctxOf msgOf (challengeOf V adv dflt ctxOf msgOf) (queryOf V adv dflt ctxOf msgOf)
      (guardedStatement V A adv dflt ctxOf msgOf stmt) hF dom
      (extractedInstance (Row.rowValid h) dom (Row.hkrow h) hr dec A stmt) hfalse H Sat Ffam
      hexact MD hfail
      (fun pre _ ct => hright_v1 (Row.rowValid h) dom (Row.hkrow h) hr dec V A adv dflt ctxOf msgOf
        stmt (Ffam pre) (MD pre) (hmatch pre) pre ct)
      ht₁ hT hT1 hcand hD)
  congr 3
  refine Finset.filter_congr fun omega _ => ?_
  rw [accepts_iff_guarded]

/-- The row opens `140` columns, so its compiler opens something. -/
theorem v8Hash_openings_pos : 0 < v8Hash.params.row.openings := by decide

/--
**The depth-16, `2^18`-wire row at the compiled Longfellow verifier.**

`row_fs_ratio_le_v1` at `CertifiedV1.v8Hash` (the deployed hash profile, 20 layers and 610 sumcheck slots,
over `GF(2^128)`, Ligero V1 at the deployed geometry with 132 opened columns), with the numerals of
`CertifiedV1.v8Hash_fs_ratio_le`:

```text
Pr[ Accepts (v1K …) V A codec adv dflt ctxOf msgOf stmt  ∧  Fails ]  ≤  2^-114  +  N · 2^-115
```

over the hash tape and a challenge tape of `595 + N` slots, against an `N`-query search.  The
premises are `row_fs_ratio_le_v1`'s; `hr` is discharged (`openings = 140`).
-/
theorem v8Hash_compiled_fs_ratio_le
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Enc D Salt Aux Aux' : Type} {respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt (Col F v8Hash.params.nw v8Hash.params.nq) D Enc}
    (dec : RoleDecoders codec)
    -- the verifier: its field code, the code's domain, and the Ligero statement
    (V : Code C F (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Msg logw logc)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q
      v8Hash.params.row.n)
    (stmt : (Fin v8Hash.tape → D) →
      LigeroFamily.ConstraintSystem F v8Hash.params.nw v8Hash.params.nq
        v8Hash.params.q Equations)
    -- the Merkle adversary and the Fiat–Shamir search, run after the commitment
    (A : Adversary Enc D Salt (Col F v8Hash.params.nw v8Hash.params.nq)
      (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
      (LigeroFamily.Response F v8Hash.params.row.openings v8Hash.params.q
        v8Hash.params.row.n 1)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Aux Aux' v8Hash.params.row.n
      v8Hash.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C v8Hash.params.nl v8Hash.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    {Fails : (Fin v8Hash.tape → D) → Prop}
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (hfalse : ∀ pre : Fin v8Hash.tape → D, Fails pre → ¬ (stmt pre).Language)
    -- the field half of LayerStep, one per commitment, with exactly balanced decoders
    (H : ∀ _pre : Fin v8Hash.tape → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin v8Hash.tape → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin v8Hash.tape → D,
      RbrSplit.FieldData C F
        (LigeroV1LayerStep.Chal F Equations v8Hash.params.nw v8Hash.params.nq)
        (LigeroV1LayerStep.Qry v8Hash.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin v8Hash.tape → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin v8Hash.tape → D, MsgData C Msg (H pre))
    (hmatch : ∀ pre : Fin v8Hash.tape → D, Matches V (Ffam pre) (MD pre))
    (hfail : ∀ pre : Fin v8Hash.tape → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    -- the Merkle extractor's fuels
    (ht₁ : v8Hash.commitFuel ≤ v8Hash.tape)
    (hT : 2 * v8Hash.params.row.n + (revealFuel + respondFuel) + v8Hash.commitFuel
      ≤ v8Hash.tape)
    (hT1 : 1 ≤ v8Hash.tape)
    (hcand : Fintype.card Cand = v8Hash.cardCand)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun omega : (Fin v8Hash.tape → D) × (Fin (v8Hash.fsLen N) → C) =>
        Accepts (v1K (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid)
            v8Hash_openings_pos) V A codec adv dflt ctxOf msgOf stmt omega ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin v8Hash.tape → D) *
            (Fintype.card C : ℚ) ^ (v8Hash.fsLen N))
      ≤ (1 : ℚ) / 2 ^ 114 + N * ((1 : ℚ) / 2 ^ 115) :=
  le_trans
    (row_fs_ratio_le_v1 v8Hash_valid v8Hash_openings_pos dec V dom stmt A adv dflt ctxOf
      msgOf hF hfalse H Sat Ffam hexact MD hmatch hfail ht₁ hT hT1 hcand hD)
    (add_le_add (Row.target v8Hash_valid)
      (mul_le_mul_of_nonneg_left v8Hash_fsCoefficient (Nat.cast_nonneg N)))

end Row

end Lfzk.CompiledLongfellow
