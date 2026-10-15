import Lfzk.RbrLongfellow

/-!
# The Longfellow LayerStep, with its Ligero half split off

`RbrLongfellow.LayerStepData` carries the Ligero step as six bare fields — `escaping`, `hesc`,
`accepting`, `bq`, `hbq`, and the two budget inequalities — and nothing in the repository builds
them from a Ligero theorem.  This file restates LayerStep so that they *can* be built, and
`Lfzk.LigeroV1LayerStep` then builds them from Ligero V1.

Two changes, and both are generalisations: `LayerStepData.toFieldData`, `LayerStepData.toLigeroData` and
`LayerStepData.budgets` map every `LayerStepData` into the new form, with the same transitions (`rfl`).

## 1. The query round is charged only at doomed challenges

`LayerStepData.hbq` asks for `|accepting x| ≤ bq` at **every** challenge `x`.  No Ligero theorem
proves that: `query_density_le_of_profiledDoomedAfter` bounds the accepting queries of a *doomed*
challenge, and an undoomed one may accept every query.  It does not have to: round-by-round
soundness only charges a slot from a doomed state, and at `.challenged x` doom *is*
`LigDoomed x`.  `ligeroQueryStep_budget_doomed` uses exactly that, so `LigeroData.hbq` is
quantified over doomed challenges only.

## 2. The field half and the Ligero half are separate structures

`FieldData` is `LayerStepData` minus its Ligero fields and minus its budget inequalities;
`LigeroData` is the Ligero fields; `Budgets` is the six inequalities.  The Ligero half then depends
on the commitment through its doom predicate, which a single `LayerStepData` family cannot express —
`Lfzk.Certified.Row.nizk_ratio_le_longfellow` fixes `LigDoomed` across commitments, while a Ligero
classifier is a function of the committed oracle.

## 3. `LayerStepData` at a one-coin pair budget is empty

`LayerStepData.two_card_le_bpair`: any `LayerStepData` over a non-empty coin space has
`2 · |F| ≤ bpair`, because layer 0's pair decoder `C → F × F` has some non-empty fibre, so its
balance `kpair` is at least one and `hbp0 : kpair · 2|F| ≤ bpair`.  So at `bpair < 2|F|` there is
no `LayerStepData` at all (`LayerStepData.isEmpty_of_bpair_lt`), and a theorem quantified over a family of
them holds vacuously.  `Lfzk.CertifiedV1` applies this to the rows of `Lfzk.Certified`.

## What is still a hypothesis here

Exactly what `RbrLongfellow.layerStep_ratio_le` leaves: `hfail` (extraction failure means no candidate
satisfies the circuit) and `hright` (acceptance implies LayerStep reaches `.accepted`).
`LayerStepAccepts` states the latter without mentioning any doom predicate, so a caller can discharge it
without knowing the Ligero classifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrSplit

open Finset Sumcheck
open scoped Classical
open RbrLongfellow

variable {C F X Cand : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {Witness : Type} {nc nv logw logc : ℕ}

/-! ## The query round at a doomed challenge -/

omit [Fintype F] [DecidableEq F] in
/--
**The Ligero query round's budget, from a doomed state: `k * bq`.**

`RbrLongfellow.ligeroQueryStep_budget` with its uniform `hbq` weakened to doomed challenges.  The
state is `.challenged x` with `LigDoomed x` — that is what doom means there — so only the doomed
challenges' accepting sets are ever counted.  Every other state rejects, as before.
-/
theorem ligeroQueryStep_budget_doomed [SumcheckInterp F] {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (decodeQuery : C → Q) (k : ℕ)
    (hbal : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ k)
    (accepting : X → Finset Q) (bq : ℕ)
    (hbq : ∀ x : X, LigDoomed x → (accepting x).card ≤ bq)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X) (hw : Wrong H Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (ligeroQueryStep decodeQuery accepting c s)).card
      ≤ k * bq := by
  classical
  cases s with
  | challenged x =>
      have hx : LigDoomed x := hw
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        decodeQuery c ∈ accepting x) ?_) ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        by_contra hnot
        simp only [ligeroQueryStep, if_neg hnot, Wrong, not_true] at hc
      · exact le_trans (Bcs.card_preimage_le_of_balanced decodeQuery k hbal (accepting x))
          (Nat.mul_le_mul_left k (hbq x hx))
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | running _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc

/-! ## The two halves -/

/--
**The field half of LayerStep.**  `RbrLongfellow.LayerStepData` without its Ligero fields and without
its budget inequalities: the circuit, the honest-claim facts at layer 0, the transitions' data,
and the four decoders with their fibre bounds.
-/
structure FieldData (C F X Q Cand Witness : Type) [Fintype C] [Field F] [Fintype F]
    [DecidableEq F] [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (nc nv logw logc : ℕ) (H : Honest F Cand logw logc) (Sat : Cand → Prop) where
  /-- The circuit LayerStep is about. -/
  LC : LayeredCircuit Witness nc nv logw logc F
  /-- Each candidate's witness. -/
  wOf : Cand → Witness
  /-- The input layer's tail. -/
  tail : ℕ → F
  /-- Layer 0's incoming state. -/
  st0 : LayerState logw logc F
  /-- The layer boundary, as a function of the prefix. -/
  B : ∀ m : ℕ, (Fin m → C) → Boundary H
  /-- The prover's round polynomials, as a function of the prefix. -/
  prover : ∀ m : ℕ, (Fin m → C) →
    ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2
  /-- `begin_layer`'s coin decoder: the layer's two points. -/
  decodePair : C → F × F
  /-- The field-element decoder, used by every sumcheck round and every boundary. -/
  decodeF : C → F
  /-- Ligero's linear-combination decoder. -/
  decodeChal : C → X
  /-- Ligero's query decoder. -/
  decodeQuery : C → Q
  /-- `decodePair`'s balance. -/
  kpair : ℕ
  /-- `decodeF`'s balance. -/
  k : ℕ
  /-- `decodeChal`'s balance. -/
  kchal : ℕ
  /-- `decodeQuery`'s balance. -/
  kq : ℕ
  hbalPair : ∀ y : F × F, (univ.filter fun c : C => decodePair c = y).card ≤ kpair
  hbalF : ∀ y : F, (univ.filter fun c : C => decodeF c = y).card ≤ k
  hbalChal : ∀ y : X, (univ.filter fun c : C => decodeChal c = y).card ≤ kchal
  hbalQuery : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ kq
  /-- The run starts from claims of zero (`verifier_layers.h:L70`). -/
  hzero0 : st0.claim0 = 0
  /-- The run starts from claims of zero. -/
  hzero1 : st0.claim1 = 0
  /-- `H.sum` at layer 0 is the layer claim, so an escape there is `Degenerate`. -/
  hclaim : ∀ (cand : Cand) (b a : F),
    H.sum cand 0 st0 b a [] = layer_claim (nc := nc) (nv := nv) (LC.Quad 0 b)
      (LC.V 1 (wOf cand) tail) a st0.q st0.g0 st0.g1
  /-- An unsatisfied circuit's honest claim does not vanish on all of `F × F`
  (`ArithmetizedCircuit.arith`). -/
  harith : ∀ cand : Cand, ¬ Sat cand →
    ¬ (layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 1
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 1
          st0.q st0.g0 st0.g1 = 0)

/--
**The Ligero half of LayerStep**, at a doom predicate on Ligero challenges.

`accepting` is the query test, as a function of the prefix and the challenge; `escaping` contains
every undoomed challenge; `bq` bounds the accepting set of every **doomed** challenge.
-/
structure LigeroData (C X Q : Type) (LigDoomed : X → Prop) where
  /-- The queries the opened columns pass, as a function of the prefix and the challenge. -/
  accepting : ∀ m : ℕ, (Fin m → C) → X → Finset Q
  /-- The Ligero challenges that do not doom the run. -/
  escaping : Finset X
  hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping
  /-- A bound on a doomed challenge's accepting-query count. -/
  bq : ℕ
  hbq : ∀ (m : ℕ) (pref : Fin m → C) (x : X), LigDoomed x → (accepting m pref x).card ≤ bq

section Halves

variable [SumcheckInterp F] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {nl : ℕ} {w : ℕ → ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}

/-- The six budget inequalities `RbrLongfellow.LayerStepData` carries, against the split data. -/
structure Budgets (FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (LD : LigeroData C X Q LigDoomed) (bpair bround bin blig bquery : ℕ) : Prop where
  /-- `layerPair 0` is `initStep`, which costs `kpair · 2|F|`. -/
  hbp0 : FD.kpair * (2 * Fintype.card F) ≤ bpair
  /-- A later `layerPair` is `combineStep`, which costs `k`. -/
  hbp1 : FD.k * 1 ≤ bpair
  hbround : FD.k * 2 ≤ bround
  hbin : FD.k * 1 ≤ bin
  hblig : FD.kchal * LD.escaping.card ≤ blig
  hbquery : FD.kq * LD.bq ≤ bquery

/-- The transitions, at a field half and a query test.  Literally `RbrLongfellow.lfSteps`, so the
LayerStep is the one `RbrLongfellow` defines. -/
noncomputable def stepsOf (FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (accepting : ∀ m : ℕ, (Fin m → C) → X → Finset Q) : RbrLayerStep.Steps C F X logw logc nl w :=
  lfSteps (H := H) (nl := nl) (w := w) FD.st0 FD.B FD.prover FD.decodePair FD.decodeF
    FD.decodeChal FD.decodeQuery accepting

/-- The transitions the two halves define. -/
noncomputable def steps (FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (LD : LigeroData C X Q LigDoomed) : RbrLayerStep.Steps C F X logw logc nl w :=
  stepsOf (nl := nl) (w := w) FD LD.accepting

/-! ### Acceptance, without a doom predicate -/

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] in
/-- Two claim chains with the same start and the same transitions visit the same states: the
state function never reads `Wrong`, or the candidate type. -/
theorem state_eq_of {T : ℕ} {S Cand₁ Cand₂ : Type} (ch₁ : Bcs.ClaimChain C T S Cand₁)
    (ch₂ : Bcs.ClaimChain C T S Cand₂) (hi : ch₁.init = ch₂.init) (hs : ch₁.step = ch₂.step) :
    ∀ (j : ℕ) (p : Fin j → C), ch₁.state j p = ch₂.state j p
  | 0, _ => hi
  | j + 1, p => by
      rw [Bcs.ClaimChain.state, Bcs.ClaimChain.state, hs, state_eq_of ch₁ ch₂ hi hs j]

/--
**LayerStep reaches `.accepted`**, stated with no doom predicate and no candidate type.

`RbrLongfellow.Accepts` is the same event (`accepts_of_layerStepAccepts`), but its statement mentions
`Wrong H Sat LigDoomed`; when `LigDoomed` comes from a Ligero classifier that only exists under the
false-statement premise, a caller cannot name it.  This one it can.
-/
noncomputable def LayerStepAccepts (steps : RbrLayerStep.Steps C F X logw logc nl w)
    (tape : Fin (Rounds.Role.length nl w) → C) : Prop :=
  (RbrLayerStep.layerStepChain (Cand := PUnit) steps (fun _ _ => False)
      (.start : RbrLayerStep.WState logw logc F X)).state (Rounds.Role.length nl w)
    (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl) = .accepted

omit [Fintype C] [Fintype F] [DecidableEq F] [DecidableEq X] in
theorem accepts_of_layerStepAccepts (steps : RbrLayerStep.Steps C F X logw logc nl w)
    {tape : Fin (Rounds.Role.length nl w) → C} (h : LayerStepAccepts steps tape) :
    Accepts (H := H) Sat LigDoomed steps tape := by
  unfold Accepts layerStepFinal
  rw [state_eq_of (RbrLayerStep.layerStepChain steps (Wrong H Sat LigDoomed)
      (.start : RbrLayerStep.WState logw logc F X))
    (RbrLayerStep.layerStepChain (Cand := PUnit) steps (fun _ _ => False)
      (.start : RbrLayerStep.WState logw logc F X)) rfl rfl]
  exact h

omit [Fintype C] [Fintype F] [DecidableEq F] [DecidableEq X] in
/-- **`right_of_accepts` from `LayerStepAccepts`.**  The obligation, for any doom predicate, from the
doom-free acceptance implication. -/
theorem rightOfAccepts_of_layerStepAccepts [Nonempty Cand] (steps : RbrLayerStep.Steps C F X logw logc nl w)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (hle : ∀ tape, Acc tape → LayerStepAccepts steps tape) :
    RightOfAccepts (H := H) Sat LigDoomed steps Acc :=
  rightOfAccepts_of_imp (H := H) Sat LigDoomed steps
    fun tape hacc => accepts_of_layerStepAccepts (H := H) (Sat := Sat) (LigDoomed := LigDoomed) steps
      (hle tape hacc)

/-! ### The six budgets -/

namespace FieldData

variable (FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat)
variable (LD : LigeroData C X Q LigDoomed)
variable {bpair bround bin blig bquery : ℕ}

theorem budget_pair (hB : Budgets FD LD bpair bround bin blig bquery) :
    ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
      (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand ((steps (w := w) FD LD).pair ly m pref c s)).card
        ≤ bpair := by
  intro ly m pref cand s hw
  by_cases hly : ly.val = 0
  · simp only [steps, stepsOf, lfSteps, if_pos hly]
    exact le_trans (initStep_budget H Sat LigDoomed FD.LC FD.wOf FD.tail FD.st0 FD.decodePair
      FD.kpair FD.hbalPair FD.hzero0 FD.hzero1 FD.hclaim cand (FD.harith cand) s hw) hB.hbp0
  · simp only [steps, stepsOf, lfSteps, if_neg hly]
    exact le_trans
      (combineStep_budget Sat LigDoomed (FD.B m pref) FD.decodeF FD.k FD.hbalF cand s hw) hB.hbp1

theorem budget_round (hB : Budgets FD LD bpair bround bin blig bquery) :
    ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C)
      (cand : Cand) (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
      (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand ((steps FD LD).round ly j m pref c s)).card ≤ bround := by
  intro ly j m pref cand s hw
  exact le_trans
    (roundStep_budget H Sat LigDoomed (FD.prover m pref) FD.decodeF FD.k FD.hbalF cand s hw)
    hB.hbround

theorem budget_in (hB : Budgets FD LD bpair bround bin blig bquery) :
    ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
      (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand ((steps (nl := nl) (w := w) FD LD).inputBind m pref c s)).card
        ≤ bin := by
  intro m pref cand s hw
  exact le_trans
    (combineStep_budget Sat LigDoomed (FD.B m pref) FD.decodeF FD.k FD.hbalF cand s hw) hB.hbin

theorem budget_lig (hB : Budgets FD LD bpair bround bin blig bquery) :
    ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
      (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand
          ((steps (nl := nl) (w := w) FD LD).ligeroChallenge m pref c s)).card ≤ blig := by
  intro m pref cand s _
  exact le_trans (ligeroChallengeStep_budget H Sat LigDoomed FD.decodeChal FD.kchal FD.hbalChal
    LD.escaping LD.hesc cand s) hB.hblig

/-- The query budget, and the one place the doom hypothesis `hw` is used by a Ligero slot. -/
theorem budget_query (hB : Budgets FD LD bpair bround bin blig bquery) :
    ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
      (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand
          ((steps (nl := nl) (w := w) FD LD).ligeroQuery m pref c s)).card ≤ bquery := by
  intro m pref cand s hw
  exact le_trans (ligeroQueryStep_budget_doomed H Sat LigDoomed FD.decodeQuery FD.kq FD.hbalQuery
    (LD.accepting m pref) LD.bq (LD.hbq m pref) cand s hw) hB.hbquery

/--
**The split LayerStep, as a round-by-round argument.**  `RbrLayerStep.layerStepRbr` at the six budgets above;
`wrong_init` is `hfail` and `right_of_accepts` is `hright`.
-/
noncomputable def rbr [DecidableEq C] [Nonempty C] [Fintype Cand]
    (hB : Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed (steps FD LD) Acc) :
    Bcs.Rbr C (Rounds.Role.length nl w) Acc Fails :=
  RbrLayerStep.layerStepRbr (steps FD LD) (Wrong H Sat LigDoomed)
    (.start : RbrLayerStep.WState logw logc F X) bpair bround bin blig bquery
    (fun hf cand => hfail hf cand)
    (FD.budget_pair LD hB) (FD.budget_round LD hB) (FD.budget_in LD hB) (FD.budget_lig LD hB)
    (FD.budget_query LD hB) hright

/-- Its per-slot budget is the class budget, times the list factor once. -/
theorem rbr_beta [DecidableEq C] [Nonempty C] [Fintype Cand]
    (hB : Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed (steps FD LD) Acc) :
    (FD.rbr LD hB (Fails := Fails) hfail hright).beta
      = fun i => Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i) := rfl

/-- **The split form of `layerStep_ratio_le`.** -/
theorem ratio_le [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    (hB : Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ tape, Acc tape → LayerStepAccepts (steps (nl := nl) (w := w) FD LD) tape)
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Acc tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) :=
  RbrLayerStep.layerStep_ratio_le (Accepts := Acc) (Fails := Fails) (steps FD LD) (Wrong H Sat LigDoomed)
    (.start : RbrLayerStep.WState logw logc F X) bpair bround bin blig bquery
    (fun hf cand => hfail hf cand)
    (FD.budget_pair LD hB) (FD.budget_round LD hB) (FD.budget_in LD hB) (FD.budget_lig LD hB)
    (FD.budget_query LD hB) (rightOfAccepts_of_layerStepAccepts (steps FD LD) hright) hT

end FieldData

/-! ### Every `LayerStepData` is an instance -/

variable {bpair bround bin blig bquery : ℕ}
variable (D : LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
  bpair bround bin blig bquery)

/-- `LayerStepData`'s field half. -/
def _root_.Lfzk.RbrLongfellow.LayerStepData.toFieldData :
    FieldData C F X Q Cand Witness nc nv logw logc H Sat where
  LC := D.LC
  wOf := D.wOf
  tail := D.tail
  st0 := D.st0
  B := D.B
  prover := D.prover
  decodePair := D.decodePair
  decodeF := D.decodeF
  decodeChal := D.decodeChal
  decodeQuery := D.decodeQuery
  kpair := D.kpair
  k := D.k
  kchal := D.kchal
  kq := D.kq
  hbalPair := D.hbalPair
  hbalF := D.hbalF
  hbalChal := D.hbalChal
  hbalQuery := D.hbalQuery
  hzero0 := D.hzero0
  hzero1 := D.hzero1
  hclaim := D.hclaim
  harith := D.harith

/-- `LayerStepData`'s Ligero half.  Its uniform `hbq` is in particular a bound at doomed challenges. -/
def _root_.Lfzk.RbrLongfellow.LayerStepData.toLigeroData : LigeroData C X Q LigDoomed where
  accepting := D.accepting
  escaping := D.escaping
  hesc := D.hesc
  bq := D.bq
  hbq m pref x _ := D.hbq m pref x

theorem _root_.Lfzk.RbrLongfellow.LayerStepData.budgets :
    Budgets D.toFieldData D.toLigeroData bpair bround bin blig bquery :=
  ⟨D.hbp0, D.hbp1, D.hbround, D.hbin, D.hblig, D.hbquery⟩

/-- **Same transitions.**  The split LayerStep at a `LayerStepData`'s halves is that `LayerStepData`'s LayerStep. -/
theorem _root_.Lfzk.RbrLongfellow.LayerStepData.steps_eq :
    steps (nl := nl) (w := w) D.toFieldData D.toLigeroData = D.steps := rfl

end Halves

/-! ## `LayerStepData` at a small pair budget is empty -/

section Empty

variable [SumcheckInterp F] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {nl : ℕ} {w : ℕ → ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable {bpair bround bin blig bquery : ℕ}

/-- **A non-empty coin space forces `2|F| ≤ bpair`.**  Some fibre of `decodePair` is non-empty, so
`kpair ≥ 1`, and `hbp0` is `kpair · 2|F| ≤ bpair`. -/
theorem _root_.Lfzk.RbrLongfellow.LayerStepData.two_card_le_bpair [Nonempty C]
    (D : LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
      bpair bround bin blig bquery) :
    2 * Fintype.card F ≤ bpair := by
  classical
  obtain ⟨c⟩ := ‹Nonempty C›
  have hfib : 1 ≤ (univ.filter fun c' : C => D.decodePair c' = D.decodePair c).card :=
    Finset.card_pos.mpr ⟨c, by simp⟩
  have hk : 1 ≤ D.kpair := le_trans hfib (D.hbalPair _)
  calc 2 * Fintype.card F = 1 * (2 * Fintype.card F) := (one_mul _).symm
    _ ≤ D.kpair * (2 * Fintype.card F) := Nat.mul_le_mul_right _ hk
    _ ≤ bpair := D.hbp0

/-- **So below `2|F|` there is no `LayerStepData` at all**, and a statement quantified over a family of
them is vacuous there. -/
theorem _root_.Lfzk.RbrLongfellow.LayerStepData.isEmpty_of_bpair_lt [Nonempty C]
    (h : bpair < 2 * Fintype.card F) :
    IsEmpty (LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
      bpair bround bin blig bquery) :=
  ⟨fun D => absurd (LayerStepData.two_card_le_bpair D) (Nat.not_le.mpr h)⟩

/-- In particular at `bpair = 1`, over any field. -/
theorem _root_.Lfzk.RbrLongfellow.LayerStepData.isEmpty_of_bpair_one [Nonempty C] :
    IsEmpty (LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
      1 bround bin blig bquery) := by
  refine LayerStepData.isEmpty_of_bpair_lt ?_
  have : 1 < Fintype.card F := Fintype.one_lt_card
  omega

end Empty


/-! ## Exactly balanced decoders

`Budgets` asks for `kchal · |escaping| ≤ blig`, and a Ligero theorem bounds `|escaping|` as a
*fraction of the challenge space*.  The two meet only through the decoder: if `decodeChal` is at
most `|C|/|X|`-to-one then `kchal · |escaping| / |C| ≤ |escaping| / |X|`.  `Exact` asks that of
all four decoders, and `Exact.field_budgets` reads the field-round budgets off it at
`|C|`-relative numerals, so that every slot's density is the protocol's own: `2/|F|`, `1/|F|`,
and the Ligero theorem's two densities.

`product_coins_exact` shows the four conditions are jointly satisfiable: the coin space
`X × Q × (F × F)` with its projections.  They do force `|C| ≥ |X|`, and for a Ligero challenge
space that is far larger than one field element. -/

section Exact

variable [SumcheckInterp F] [DecidableEq X] [Fintype X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop}

/-- **Exactly balanced decoders**: each is at most `|C| / |Y|`-to-one onto its range `Y`. -/
def FieldData.Exact (FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat) : Prop :=
  FD.kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C ∧
    FD.k * Fintype.card F ≤ Fintype.card C ∧
    FD.kchal * Fintype.card X ≤ Fintype.card C ∧
    FD.kq * Fintype.card Q ≤ Fintype.card C

/-- **The field slots' budgets, from exactness.**  At `bpair = bround = ⌊2|C|/|F|⌋` and
`bin = ⌊|C|/|F|⌋`, the four field-round inequalities of `Budgets` hold. -/
theorem FieldData.Exact.field_budgets {FD : FieldData C F X Q Cand Witness nc nv logw logc H Sat}
    (hex : FD.Exact) :
    FD.kpair * (2 * Fintype.card F) ≤ 2 * Fintype.card C / Fintype.card F ∧
      FD.k * 1 ≤ 2 * Fintype.card C / Fintype.card F ∧
      FD.k * 2 ≤ 2 * Fintype.card C / Fintype.card F ∧
      FD.k * 1 ≤ Fintype.card C / Fintype.card F := by
  have hF : 0 < Fintype.card F := Fintype.card_pos
  obtain ⟨hp, hk, -, -⟩ := hex
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Nat.le_div_iff_mul_le hF]
  · calc FD.kpair * (2 * Fintype.card F) * Fintype.card F
        = 2 * (FD.kpair * (Fintype.card F * Fintype.card F)) := by ring
      _ ≤ 2 * Fintype.card C := Nat.mul_le_mul_left 2 hp
  · calc FD.k * 1 * Fintype.card F = FD.k * Fintype.card F := by ring
      _ ≤ 2 * Fintype.card C := by omega
  · calc FD.k * 2 * Fintype.card F = 2 * (FD.k * Fintype.card F) := by ring
      _ ≤ 2 * Fintype.card C := Nat.mul_le_mul_left 2 hk
  · calc FD.k * 1 * Fintype.card F = FD.k * Fintype.card F := by ring
      _ ≤ Fintype.card C := hk

end Exact

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] in
theorem card_filter_fst_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (y : α) :
    (univ.filter fun c : α × β => c.1 = y).card ≤ Fintype.card β := by
  calc (univ.filter fun c : α × β => c.1 = y).card
      ≤ (({y} : Finset α) ×ˢ (univ : Finset β)).card :=
        Finset.card_le_card fun c hc => by
          simp only [mem_filter, mem_univ, true_and] at hc
          exact Finset.mem_product.mpr ⟨by simp [hc], mem_univ _⟩
    _ = Fintype.card β := by simp

omit [Fintype C] [Field F] [Fintype F] [DecidableEq F] in
theorem card_filter_snd_le {α β : Type} [Fintype α] [Fintype β] (p : β → Prop)
    [DecidablePred p] :
    (univ.filter fun c : α × β => p c.2).card ≤ Fintype.card α * (univ.filter p).card := by
  calc (univ.filter fun c : α × β => p c.2).card
      ≤ ((univ : Finset α) ×ˢ (univ.filter p)).card :=
        Finset.card_le_card fun c hc => by
          simp only [mem_filter, mem_univ, true_and] at hc
          exact Finset.mem_product.mpr ⟨mem_univ _, by simp [hc]⟩
    _ = Fintype.card α * (univ.filter p).card := by simp

omit [Fintype C] [Field F] in
/--
**Exactness is satisfiable.**  On the coin space `X × Q × (F × F)` the four projections —
challenge, query, pair, first field coordinate — have the stated fibre bounds, and those bounds
meet every `Exact` inequality with equality.
-/
theorem product_coins_exact [Fintype X] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q] :
    (∀ y : F × F, (univ.filter fun c : X × Q × (F × F) => c.2.2 = y).card
        ≤ Fintype.card X * Fintype.card Q) ∧
      (∀ y : F, (univ.filter fun c : X × Q × (F × F) => c.2.2.1 = y).card
        ≤ Fintype.card X * (Fintype.card Q * Fintype.card F)) ∧
      (∀ y : X, (univ.filter fun c : X × Q × (F × F) => c.1 = y).card
        ≤ Fintype.card Q * (Fintype.card F * Fintype.card F)) ∧
      (∀ y : Q, (univ.filter fun c : X × Q × (F × F) => c.2.1 = y).card
        ≤ Fintype.card X * (Fintype.card F * Fintype.card F)) ∧
      Fintype.card X * Fintype.card Q * (Fintype.card F * Fintype.card F)
        = Fintype.card (X × Q × (F × F)) ∧
      Fintype.card X * (Fintype.card Q * Fintype.card F) * Fintype.card F
        = Fintype.card (X × Q × (F × F)) ∧
      Fintype.card Q * (Fintype.card F * Fintype.card F) * Fintype.card X
        = Fintype.card (X × Q × (F × F)) ∧
      Fintype.card X * (Fintype.card F * Fintype.card F) * Fintype.card Q
        = Fintype.card (X × Q × (F × F)) := by
  classical
  simp only [Fintype.card_prod]
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_, fun y => ?_, by ring, by ring, by ring, by ring⟩
  · refine le_trans (card_filter_snd_le (fun b : Q × (F × F) => b.2 = y)) ?_
    refine Nat.mul_le_mul_left _ (le_trans (card_filter_snd_le (fun b : F × F => b = y)) ?_)
    rw [Finset.filter_eq' univ y]
    simp
  · refine le_trans (card_filter_snd_le (fun b : Q × (F × F) => b.2.1 = y)) ?_
    refine Nat.mul_le_mul_left _ (le_trans (card_filter_snd_le (fun b : F × F => b.1 = y)) ?_)
    have h1 := card_filter_fst_le (β := F) y
    exact Nat.mul_le_mul_left _ (by simpa [Fintype.card_prod] using h1)
  · simpa [Fintype.card_prod] using card_filter_fst_le (β := Q × (F × F)) y
  · refine le_trans (card_filter_snd_le (fun b : Q × (F × F) => b.1 = y)) ?_
    have h1 := card_filter_fst_le (β := F × F) y
    exact Nat.mul_le_mul_left _ (by simpa [Fintype.card_prod] using h1)

/-! ## The trivial round-by-round object

When extraction does not fail there is nothing to bound: the state function that is never doomed
satisfies every obligation, at any budget.  Used to complete a commitment-indexed family whose
members are only constructible under `Fails`. -/

/-- The never-doomed `Rbr`, at any budget, when `Fails` is false. -/
def trivialRbr {T : ℕ} {Acc : (Fin T → C) → Prop} {Fails : Prop} (hF : ¬ Fails)
    (beta : Fin T → ℕ) : Bcs.Rbr C T Acc Fails where
  doomed _ _ := False
  beta := beta
  doomed_start hf := absurd hf hF
  doom_preserved _ _ hd := hd.elim
  accepts_undoomed _ _ hd := hd

end Lfzk.RbrSplit
