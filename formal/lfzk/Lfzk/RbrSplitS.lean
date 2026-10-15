import Lfzk.RbrLayerStepS
import Lfzk.NizkGrinding

/-!
# The clear-verifier LayerStep at the mixed accounting

`Lfzk.RbrSplit` builds the Longfellow LayerStep's round-by-round object from a field half
(`FieldData`) and a Ligero half (`LigeroData`) and pays the list factor `|Cand|` at all five role
classes.  At the two Ligero slots that factor is not owed: doom at `.challenged x` is
`LigDoomed x` for **every** candidate (`RbrLongfellow.Wrong`), because the Ligero classifier's doom
is a statement about the whole lift list.  So from a doomed prefix

* the challenge slot leaves doom only at answers decoding into `escaping` — `kchal · |escaping|`
  (`ligeroChallengeStep_budget_doomedPrefix`);
* the query slot leaves doom only at answers decoding into the doomed challenge's accepting set —
  `kq · bq` (`ligeroQueryStep_budget_doomedPrefix`).

`FieldData.rbrS` is `RbrSplit.FieldData.rbr` with those two budgets and
`Lfzk.RbrLayerStepS.layerStepRbrS`'s mixed accounting; `FieldData.ratio_leS` its ratio.
`escapesAt_cardS` is `NizkGrinding.escapesAt_card` at the mixed accounting: a Fiat–Shamir query
point pays `|Cand| · b` at a field role and `blig` / `bquery` at a Ligero role.  The transitions,
the doom predicate and the state function are the existing ones (`layerStepChainS_ofSteps`), so
`NizkGrinding.DoomedAt`, `EscapesAt` and `link_at` apply unchanged.

## What is still a hypothesis here

Nothing new: the field budgets are `RbrSplit.FieldData.budget_pair/round/in`, the Ligero half is a
`RbrSplit.LigeroData` (or `NizkGrinding.MsgLigeroData`), exactly as before.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrSplitS

open Finset Sumcheck RbrLongfellow Lfzk.RbrLayerStepS
open scoped Classical

variable {C F X Cand : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {Witness : Type} {nc nv logw logc : ℕ}

/-! ## 1. The two Ligero slots from a doomed prefix -/

omit [Fintype F] [DecidableEq F] in
/-- **The Ligero challenge slot from a doomed prefix: `k · |escaping|`, no list factor.**  The state
after the slot is `.challenged x`, wrong for every candidate exactly when `LigDoomed x`. -/
theorem ligeroChallengeStep_budget_doomedPrefix [Fintype Cand] [SumcheckInterp F] [DecidableEq X]
    (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (decodeChal : C → X) (k : ℕ)
    (hbal : ∀ y : X, (univ.filter fun c : C => decodeChal c = y).card ≤ k)
    (escaping : Finset X) (hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping)
    (s : RbrLayerStep.WState logw logc F X) :
    (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong H Sat LigDoomed cand (ligeroChallengeStep decodeChal c s)).card
      ≤ k * escaping.card := by
  classical
  refine le_trans (Finset.card_le_card (t := univ.filter fun c : C => decodeChal c ∈ escaping) ?_)
    (Bcs.card_preimage_le_of_balanced decodeChal k hbal escaping)
  intro c hc
  simp only [mem_filter, mem_univ, true_and, not_forall] at hc ⊢
  obtain ⟨cand, hcand⟩ := hc
  cases s with
  | running ws => exact hesc _ (by simpa [ligeroChallengeStep, Wrong] using hcand)
  | start => simp [ligeroChallengeStep, Wrong] at hcand
  | challenged _ => simp [ligeroChallengeStep, Wrong] at hcand
  | accepted => simp [ligeroChallengeStep, Wrong] at hcand
  | failed => simp [ligeroChallengeStep, Wrong] at hcand

omit [Fintype F] [DecidableEq F] in
/-- **The Ligero query slot from a doomed prefix: `k · bq`, no list factor.**  A doomed prefix is
`.challenged x` with `LigDoomed x` (or the candidate list is empty and nothing escapes); the state
after the slot is `.accepted` only at a query in `accepting x`. -/
theorem ligeroQueryStep_budget_doomedPrefix [Fintype Cand] [SumcheckInterp F] {Q : Type} [Fintype Q]
    [DecidableEq Q] (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (decodeQuery : C → Q) (k : ℕ)
    (hbal : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ k)
    (accepting : X → Finset Q) (bq : ℕ)
    (hbq : ∀ x : X, LigDoomed x → (accepting x).card ≤ bq)
    (s : RbrLayerStep.WState logw logc F X) (hw : ∀ cand : Cand, Wrong H Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong H Sat LigDoomed cand
          (ligeroQueryStep decodeQuery accepting c s)).card
      ≤ k * bq := by
  classical
  cases s with
  | challenged x =>
      by_cases hne : Nonempty Cand
      · obtain ⟨cand0⟩ := hne
        have hx : LigDoomed x := hw cand0
        refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
          decodeQuery c ∈ accepting x) ?_)
          (le_trans (Bcs.card_preimage_le_of_balanced decodeQuery k hbal (accepting x))
            (Nat.mul_le_mul_left k (hbq x hx)))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, not_forall] at hc ⊢
        obtain ⟨cand, hcand⟩ := hc
        by_contra hnot
        simp only [ligeroQueryStep, if_neg hnot, Wrong, not_true] at hcand
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, not_forall] at hc
        obtain ⟨cand, _⟩ := hc
        exact absurd ⟨cand⟩ hne
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc
      obtain ⟨cand, hcand⟩ := hc
      simp [ligeroQueryStep, Wrong] at hcand
  | running _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc
      obtain ⟨cand, hcand⟩ := hc
      simp [ligeroQueryStep, Wrong] at hcand
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc
      obtain ⟨cand, hcand⟩ := hc
      simp [ligeroQueryStep, Wrong] at hcand
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc
      obtain ⟨cand, hcand⟩ := hc
      simp [ligeroQueryStep, Wrong] at hcand

/-! ## 2. The split LayerStep at the mixed accounting -/

section Split

variable [SumcheckInterp F] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {nl : ℕ} {w : ℕ → ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable {bpair bround bin blig bquery : ℕ}

namespace FieldData

variable (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
variable (LD : RbrSplit.LigeroData C X Q LigDoomed)

/-- The Ligero challenge slot's doomed-prefix budget, at the split data. -/
theorem budget_ligS [Fintype Cand] (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery) :
    ∀ (m : ℕ) (pref : Fin m → C) (s : RbrLayerStep.WState logw logc F X),
      (∀ cand : Cand, Wrong H Sat LigDoomed cand s) →
      (univ.filter fun c : C => ¬ ∀ cand : Cand, Wrong H Sat LigDoomed cand
        ((StepsS.ofSteps (RbrSplit.steps (nl := nl) (w := w) FD LD)).ligeroChallenge
          m pref c s)).card ≤ blig :=
  fun _ _ s _ => le_trans (ligeroChallengeStep_budget_doomedPrefix H Sat LigDoomed FD.decodeChal
    FD.kchal FD.hbalChal LD.escaping LD.hesc s) hB.hblig

/-- The Ligero query slot's doomed-prefix budget, at the split data. -/
theorem budget_queryS [Fintype Cand] (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery) :
    ∀ (m : ℕ) (pref : Fin m → C) (s : RbrLayerStep.WState logw logc F X),
      (∀ cand : Cand, Wrong H Sat LigDoomed cand s) →
      (univ.filter fun c : C => ¬ ∀ cand : Cand, Wrong H Sat LigDoomed cand
        ((StepsS.ofSteps (RbrSplit.steps (nl := nl) (w := w) FD LD)).ligeroQuery
          m pref c s)).card ≤ bquery :=
  fun m pref s hw => le_trans (ligeroQueryStep_budget_doomedPrefix H Sat LigDoomed FD.decodeQuery
    FD.kq FD.hbalQuery (LD.accepting m pref) LD.bq (LD.hbq m pref) s hw) hB.hbquery

/--
**The split LayerStep at the mixed accounting, as a round-by-round argument.**  The field slots
pay `|Cand| · b`, the two Ligero slots `blig` and `bquery`.
-/
noncomputable def rbrS [Fintype Cand] (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed (RbrSplit.steps FD LD) Acc) :
    Bcs.Rbr C (Rounds.Role.length nl w) Acc Fails :=
  layerStepRbrS (StepsS.ofSteps (RbrSplit.steps (nl := nl) (w := w) FD LD)) (Wrong H Sat LigDoomed)
    (.start : RbrLayerStep.WState logw logc F X) bpair bround bin blig bquery
    (fun hf cand => hfail hf cand)
    (RbrSplit.FieldData.budget_pair (nl := nl) (w := w) FD LD hB)
    (RbrSplit.FieldData.budget_round (nl := nl) (w := w) FD LD hB)
    (RbrSplit.FieldData.budget_in (nl := nl) (w := w) FD LD hB)
    (budget_ligS (nl := nl) (w := w) FD LD hB) (budget_queryS (nl := nl) (w := w) FD LD hB)
    (by rw [layerStepChainS_ofSteps]; exact hright)

/-- `rbrS`'s doom is the existing LayerStep's. -/
theorem rbrS_doomed [Fintype Cand] (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed (RbrSplit.steps FD LD) Acc) :
    (rbrS FD LD hB hfail hright).doomed
      = (RbrLayerStep.layerStepChain (RbrSplit.steps (nl := nl) (w := w) FD LD)
          (Wrong H Sat LigDoomed) .start).doomed := by
  show (layerStepChainS _ _ _).doomed = _
  rw [layerStepChainS_ofSteps]

/-- `rbrS`'s per-slot budget is the mixed budget. -/
theorem rbrS_beta [Fintype Cand] (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed (RbrSplit.steps FD LD) Acc) :
    (rbrS FD LD hB hfail hright).beta
      = fun i => mixedBudget (nl := nl) (w := w) (Fintype.card Cand) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i) := rfl

/-- **The split LayerStep's ratio at the mixed accounting.**

```text
Pr[ accept ∧ fail ]  ≤  ( |Cand| · (nl·bpair + (∑ w)·bround + bin) + blig + bquery ) / |C|
```
-/
theorem ratio_leS [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    (hB : RbrSplit.Budgets FD LD bpair bround bin blig bquery)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ tape, Acc tape → RbrSplit.LayerStepAccepts (RbrSplit.steps (nl := nl) (w := w) FD LD) tape)
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Acc tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
            + blig + bquery : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  have h := (rbrS FD LD hB hfail
    (RbrSplit.rightOfAccepts_of_layerStepAccepts _ hright)).toCore.rbr_ratio_le hT
  have hsum : ∑ i, (rbrS FD LD hB hfail
      (RbrSplit.rightOfAccepts_of_layerStepAccepts _ hright)).toCore.beta i
      = Fintype.card Cand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
          + blig + bquery :=
    mixed_budget_sum (nl := nl) (w := w) _ _ _ _ _ _
  rwa [hsum] at h

end FieldData

end Split

/-! ## 3. A Fiat–Shamir query point's budget at the mixed accounting -/

section Points

open Lfzk.NizkGrinding

variable [SumcheckInterp F] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {Msg Ctx : Type} [Inhabited Msg]
variable {nl : ℕ} {w : ℕ → ℕ}
variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable {bpair bround bin blig bquery : ℕ}

/--
**A point's escape budget at the mixed accounting**: `mixedBudget |Cand| … role` — `|Cand| · b` at
a field role, `blig` / `bquery` at a Ligero role.  `NizkGrinding.escapesAt_card` with the list factor
dropped at the Ligero roles: LayerStep's doom preservation at the point's messages, read at the
point's slot, from `FieldData.rbrS`.
-/
theorem escapesAt_cardS [Fintype Cand]
    (FD : RbrSplit.FieldData C F X Q Cand Witness nc nv logw logc H Sat)
    (MD : MsgData C Msg H) (ML : MsgLigeroData C X Q Msg LigDoomed)
    (hB : MsgBudgets FD ML bpair bround bin blig bquery) (dflt : C)
    (p : Point Ctx Msg C nl w) (hp : DoomedAt FD MD ML dflt p) :
    (univ.filter fun c : C => EscapesAt FD MD ML dflt p c).card
      ≤ mixedBudget (nl := nl) (w := w) (Fintype.card Cand) bpair bround bin blig bquery p.role := by
  set ms := listMsgs p.msgs
  let R := FieldData.rbrS (nl := nl) (w := w) (withMsgs FD MD ms) (withMsgsL ML ms)
    (hB.withMsgs MD ms) (Acc := fun _ => False) (Fails := False) False.elim
    (fun _ h => h.elim)
  have hd : R.doomed p.role.slot (listPrefix dflt p.chals p.role.slot) := by
    show (layerStepChainS _ _ _).doomed _ _
    rw [layerStepChainS_ofSteps]
    exact hp
  have h := R.doom_preserved p.role.index (listPrefix dflt p.chals p.role.slot) hd
  rw [show R.beta p.role.index
      = mixedBudget (nl := nl) (w := w) (Fintype.card Cand) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm p.role.index) from rfl,
    indexEquiv_symm_index] at h
  refine le_trans (Finset.card_le_card ?_) h
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc ⊢
  show ¬ (layerStepChainS _ _ _).doomed _ _
  rw [layerStepChainS_ofSteps]
  exact hc

end Points

end Lfzk.RbrSplitS
