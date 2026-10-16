import Lfzk.RbrLayerStep

/-!
# LayerStep, round by round, with the list factor paid only where it is owed

`Lfzk.RbrLayerStep.layerStep_ratio_le` takes every slot's budget **per candidate** and pays the list
factor `|Cand|` at every slot (`Bcs.ClaimChain.doom_preserved_of_perCandidate`).  That is the right
price at a field slot, where each candidate has its own honest claim and a challenge that escapes
for one candidate may not escape for another.  It is a spurious price at a slot whose doom predicate
is **already a statement about the whole candidate list**: Ligero's classifier dooms a challenge
for the whole lift list at once (`NoDecodedSolution`), so from a doomed prefix at most `kchal ·
|escaping|` answers escape, with no factor `|Cand|`.

This file is the round-by-round chain with both kinds of slot.

* `chainRbr` — a `Bcs.ClaimChain` is a `Bcs.Rbr` as soon as each slot's doom preservation is given,
  in whatever form; `doomPres_of_perCandidate` (the union bound, `|Cand| · b`) and
  `doomPres_of_doomed` (a doomed-prefix count, `b`) are the two forms.
* `StepsS` — `RbrLayerStep.Steps` over an **arbitrary state type** `S`, so that a LayerStep whose
  state carries more than `RbrLayerStep.WState` (the zero-knowledge chain's pad-free state, the
  emitted rows) uses the same schedule and the same accounting; `StepsS.ofSteps` embeds the existing
  transitions, and `layerStepChainS_ofSteps` says the chain is the existing one.
* `mixedBudget` — the per-slot budget: `|Cand| · b` at the three field classes, `blig` and
  `bquery` at the two Ligero slots.  It *is* `RbrLayerStep.classBudget` at pre-multiplied field
  budgets, so every existing sum and max lemma about `classBudget` applies.
* `layerStepRbrS`, `layerStep_ratio_le_mixed`, `layerStep_ratio_le_mixed_prod` — the chain, its
  ratio, and its sum over commitments:

```text
Pr[ accept ∧ fail ]  ≤  ( |Cand| · (nl·bpair + (∑ w)·bround + bin)  +  blig  +  bquery ) / |C|
```

## What is a hypothesis here

The five budgets, exactly as in `RbrLayerStep.layerStep_ratio_le`, except that the two Ligero ones are
stated **from a doomed state** (`∀ cand, Wrong cand s`) and count the answers after which the state
is not doomed (`¬ ∀ cand, Wrong cand s'`).  `Lfzk.RbrSplitS` discharges them for the existing
LayerStep, whose doom at `.challenged x` is the candidate-independent `LigDoomed x`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrLayerStepS

open Finset
open scoped Classical

/-! ## 1. A claim chain with slot-wise doom preservation -/

section Generic

variable {C S Cand : Type} [Fintype C] {T : ℕ}

/-- **The union bound at one slot**: a per-candidate budget `b` is a doomed-prefix budget
`|Cand| · b`.  `Bcs.ClaimChain.doom_preserved_of_perCandidate`, restated in the shape `chainRbr`
takes. -/
theorem doomPres_of_perCandidate [Fintype Cand] (ch : Bcs.ClaimChain C T S Cand) (b : ℕ)
    (i : Fin T) (pref : Fin i.val → C)
    (hb : ∀ cand : Cand, ch.Wrong cand (ch.state i.val pref) →
      (univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ b)
    (hdoom : ch.doomed i.val pref) :
    (univ.filter fun c : C => ¬ ch.doomed (i.val + 1) (Bcs.extend pref c)).card
      ≤ Fintype.card Cand * b :=
  ch.doom_preserved_of_perCandidate b i pref hb hdoom

/-- **A doomed-prefix budget at one slot**: if from a state wrong for every candidate at most `b`
answers lead to a state that is not wrong for every candidate, then doom is preserved at that slot
with budget `b`, and **no list factor**. -/
theorem doomPres_of_doomed (ch : Bcs.ClaimChain C T S Cand) (b : ℕ) (i : Fin T)
    (pref : Fin i.val → C)
    (hb : (∀ cand : Cand, ch.Wrong cand (ch.state i.val pref)) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ b)
    (hdoom : ch.doomed i.val pref) :
    (univ.filter fun c : C => ¬ ch.doomed (i.val + 1) (Bcs.extend pref c)).card ≤ b := by
  refine le_trans (Finset.card_le_card ?_) (hb hdoom)
  intro c hc
  simp only [mem_filter, mem_univ, true_and, Bcs.ClaimChain.doomed] at hc ⊢
  rw [Bcs.ClaimChain.state_extend] at hc
  exact hc

/-- **A claim chain is a round-by-round argument**, given each slot's doom preservation directly.
`Bcs.ClaimChain.toRbr` is the special case where every slot is per-candidate. -/
def chainRbr (ch : Bcs.ClaimChain C T S Cand) {Accepts : (Fin T → C) → Prop} {Fails : Prop}
    (beta : Fin T → ℕ)
    (wrong_init : Fails → ∀ cand : Cand, ch.Wrong cand ch.init)
    (doom_pres : ∀ (i : Fin T) (pref : Fin i.val → C), ch.doomed i.val pref →
      (univ.filter fun c : C => ¬ ch.doomed (i.val + 1) (Bcs.extend pref c)).card ≤ beta i)
    (right_of_accepts : ∀ tape : Fin T → C, Accepts tape →
      ∃ cand : Cand, ¬ ch.Wrong cand (ch.state T (Bcs.trunc tape T le_rfl))) :
    Bcs.Rbr C T Accepts Fails where
  doomed := ch.doomed
  beta := beta
  doomed_start hfail pt := by
    intro cand
    have : ch.state 0 pt = ch.init := rfl
    rw [this]
    exact wrong_init hfail cand
  doom_preserved := doom_pres
  accepts_undoomed tape hacc := by
    obtain ⟨cand, hcand⟩ := right_of_accepts tape hacc
    exact fun hdoom => hcand (hdoom cand)

end Generic

/-! ## 2. LayerStep over an arbitrary state -/

/-- The per-role transitions of a LayerStep, over a state type `S`.  `RbrLayerStep.Steps` is the
case `S = RbrLayerStep.WState logw logc F X` (`StepsS.ofSteps`). -/
structure StepsS (C S : Type) (nl : ℕ) (w : ℕ → ℕ) where
  /-- `begin_layer`: close the previous layer, combine its claims, start the sumcheck. -/
  pair : Fin nl → ∀ m : ℕ, (Fin m → C) → C → S → S
  /-- One sumcheck round of a layer. -/
  round : ∀ ly : Fin nl, Fin (w ly.val) → ∀ m : ℕ, (Fin m → C) → C → S → S
  /-- The input binding. -/
  inputBind : ∀ m : ℕ, (Fin m → C) → C → S → S
  /-- Ligero's linear-combination challenge. -/
  ligeroChallenge : ∀ m : ℕ, (Fin m → C) → C → S → S
  /-- Ligero's query set. -/
  ligeroQuery : ∀ m : ℕ, (Fin m → C) → C → S → S

section Chain

variable {C S Cand : Type} [Fintype C] {nl : ℕ} {w : ℕ → ℕ}

/-- The existing transitions, as state-generic ones. -/
def StepsS.ofSteps {F X : Type} {logw logc : ℕ}
    (steps : RbrLayerStep.Steps C F X logw logc nl w) :
    StepsS C (RbrLayerStep.WState logw logc F X) nl w :=
  ⟨steps.pair, steps.round, steps.inputBind, steps.ligeroChallenge, steps.ligeroQuery⟩

/-- The transition a role calls for. -/
def stepAtS (steps : StepsS C S nl w) (rl : Rounds.Role nl w) (m : ℕ) (pref : Fin m → C)
    (c : C) (s : S) : S :=
  match rl with
  | .layerPair ly => steps.pair ly m pref c s
  | .sumcheck ly j => steps.round ly j m pref c s
  | .inputBind => steps.inputBind m pref c s
  | .ligeroChallenge => steps.ligeroChallenge m pref c s
  | .ligeroQuery => steps.ligeroQuery m pref c s

/-- **LayerStep as a claim chain, over any state.**  Slot `i` runs the transition of the role
`Rounds.Role.indexEquiv.symm i`. -/
noncomputable def layerStepChainS (steps : StepsS C S nl w) (Wrong : Cand → S → Prop) (init : S) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) S Cand where
  init := init
  step i pref c s := stepAtS steps (Rounds.Role.indexEquiv.symm i) i.val pref c s
  Wrong := Wrong

omit [Fintype C] in
theorem stepAtS_ofSteps {F X : Type} {logw logc : ℕ}
    (steps : RbrLayerStep.Steps C F X logw logc nl w) (rl : Rounds.Role nl w) :
    stepAtS (StepsS.ofSteps steps) rl = RbrLayerStep.stepAt steps rl := by
  cases rl <;> rfl

omit [Fintype C] in
/-- **The embedded chain is the existing one.** -/
theorem layerStepChainS_ofSteps {F X : Type} {logw logc : ℕ}
    (steps : RbrLayerStep.Steps C F X logw logc nl w)
    (Wrong : Cand → RbrLayerStep.WState logw logc F X → Prop)
    (init : RbrLayerStep.WState logw logc F X) :
    layerStepChainS (StepsS.ofSteps steps) Wrong init
      = RbrLayerStep.layerStepChain steps Wrong init := by
  unfold layerStepChainS RbrLayerStep.layerStepChain
  congr 1

/-- **The mixed per-slot budget**: `|Cand| · b` at the field classes, `blig` / `bquery` at the two
Ligero slots.  It is `classBudget` at pre-multiplied field budgets. -/
def mixedBudget (cardCand bpair bround bin blig bquery : ℕ) : Rounds.Role nl w → ℕ :=
  RbrLayerStep.classBudget (nl := nl) (w := w) (cardCand * bpair) (cardCand * bround)
    (cardCand * bin) blig bquery

/-- **The mixed budget, summed over the schedule.** -/
theorem mixed_budget_sum (cardCand bpair bround bin blig bquery : ℕ) :
    ∑ i : Fin (Rounds.Role.length nl w),
        mixedBudget (nl := nl) (w := w) cardCand bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i)
      = cardCand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin) + blig + bquery := by
  unfold mixedBudget
  rw [RbrLayerStep.layerStep_budget_sum]
  ring

/-- Only the two Ligero slots follow the field prefix, so a mixed budget
with zero terminal charges vanishes there. -/
theorem mixedBudget_zero_of_tail (cardCand bpair bround bin : ℕ)
    (rl : Rounds.Role nl w)
    (htail : Rounds.Role.layerBase w nl + 1 ≤ rl.slot) :
    mixedBudget cardCand bpair bround bin 0 0 rl = 0 := by
  cases rl with
  | layerPair ly =>
      have h := Rounds.Role.layer_slot_lt (w := w) ly (k := 0) (by omega)
      simp only [Rounds.Role.slot] at htail
      omega
  | sumcheck ly j =>
      have h := Rounds.Role.layer_slot_lt (w := w) ly
        (k := 1 + j.val) (by omega)
      simp only [Rounds.Role.slot] at htail
      omega
  | inputBind =>
      simp only [Rounds.Role.slot] at htail
      omega
  | ligeroChallenge => rfl
  | ligeroQuery => rfl

/-- The exact count of field-prefix escapes, before the challenge and query.
The two terminal budgets are zero, so the prefix sum is the established
field part of `mixed_budget_sum`. -/
theorem mixed_budget_field_prefix_sum (cardCand bpair bround bin : ℕ) :
    let u := Rounds.Role.layerBase w nl + 1
    ∑ i : Fin u,
      mixedBudget cardCand bpair bround bin 0 0
        (Rounds.Role.indexEquiv.symm
          (⟨i.val, by dsimp [Rounds.Role.length]; omega⟩ :
            Fin (Rounds.Role.length nl w))) =
      cardCand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin) := by
  let u := Rounds.Role.layerBase w nl + 1
  let B : Fin (u + 2) → ℕ := fun i =>
    mixedBudget cardCand bpair bround bin 0 0
      (Rounds.Role.indexEquiv.symm
        (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
          Fin (Rounds.Role.length nl w)))
  have hfull : (∑ i : Fin (u + 2), B i) =
      cardCand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin) := by
    calc
      _ = ∑ i : Fin (Rounds.Role.length nl w),
          mixedBudget cardCand bpair bround bin 0 0
            (Rounds.Role.indexEquiv.symm i) := by
        apply Finset.sum_congr rfl
        intro i _
        change mixedBudget cardCand bpair bround bin 0 0
          (Rounds.Role.indexEquiv.symm ⟨i.val, _⟩) =
            mixedBudget cardCand bpair bround bin 0 0
              (Rounds.Role.indexEquiv.symm i)
        congr 1
      _ = _ := by simpa only [zero_add, add_zero] using
        mixed_budget_sum (nl := nl) (w := w) cardCand bpair bround bin 0 0
  have htail : (∑ j : Fin 2, B (Fin.natAdd u j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hindex :
        (Rounds.Role.indexEquiv.symm
          (⟨(Fin.natAdd u j).val,
            by dsimp [Rounds.Role.length, u]; omega⟩ :
              Fin (Rounds.Role.length nl w))).slot = (Fin.natAdd u j).val := by
      have h := Rounds.Role.indexEquiv.apply_symm_apply
        (⟨(Fin.natAdd u j).val,
          by dsimp [Rounds.Role.length, u]; omega⟩ :
            Fin (Rounds.Role.length nl w))
      exact congrArg Fin.val h
    apply mixedBudget_zero_of_tail
    rw [hindex]
    dsimp [Fin.natAdd, u]
    omega
  rw [Fin.sum_univ_add] at hfull
  rw [htail, add_zero] at hfull
  convert hfull using 1
  apply Finset.sum_congr rfl
  intro i _
  change mixedBudget cardCand bpair bround bin 0 0
    (Rounds.Role.indexEquiv.symm ⟨i.val, _⟩) =
      mixedBudget cardCand bpair bround bin 0 0
        (Rounds.Role.indexEquiv.symm ⟨(Fin.castAdd 2 i).val, _⟩)
  congr 1

/-- **LayerStep as a `Bcs.Rbr`, at the mixed budgets.**  Per-candidate budgets at the three field
classes; doomed-prefix budgets at the two Ligero slots. -/
noncomputable def layerStepRbrS [Fintype Cand] (steps : StepsS C S nl w)
    (Wrong : Cand → S → Prop) (init : S) (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, Wrong cand init)
    (budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S),
      Wrong cand s → (univ.filter fun c : C => ¬ Wrong cand (steps.pair ly m pref c s)).card
        ≤ bpair)
    (budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.round ly j m pref c s)).card ≤ bround)
    (budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.inputBind m pref c s)).card ≤ bin)
    (budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroChallenge m pref c s)).card ≤ blig)
    (budget_query : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroQuery m pref c s)).card ≤ bquery)
    (right_of_accepts : ∀ tape : Fin (Rounds.Role.length nl w) → C, Accepts tape →
      ∃ cand : Cand, ¬ (layerStepChainS steps Wrong init).Wrong cand
        ((layerStepChainS steps Wrong init).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl))) :
    Bcs.Rbr C (Rounds.Role.length nl w) Accepts Fails :=
  chainRbr (layerStepChainS steps Wrong init)
    (fun i => mixedBudget (nl := nl) (w := w) (Fintype.card Cand) bpair bround bin blig bquery
      (Rounds.Role.indexEquiv.symm i))
    wrong_init
    (by
      intro i pref hdoom
      cases hrole : Rounds.Role.indexEquiv.symm i with
      | layerPair ly =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_perCandidate _ bpair i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_pair ly i.val pref cand _ hw
      | sumcheck ly j =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_perCandidate _ bround i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_round ly j i.val pref cand _ hw
      | inputBind =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_perCandidate _ bin i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_in i.val pref cand _ hw
      | ligeroChallenge =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_doomed _ blig i pref (fun hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_lig i.val pref _ hw
      | ligeroQuery =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_doomed _ bquery i pref (fun hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_query i.val pref _ hw)
    right_of_accepts

/-- `layerStepRbrS`'s doom is the chain's. -/
theorem layerStepRbrS_doomed [Fintype Cand] (steps : StepsS C S nl w)
    (Wrong : Cand → S → Prop) (init : S) (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init budget_pair budget_round budget_in budget_lig budget_query right_of_accepts) :
    (layerStepRbrS steps Wrong init bpair bround bin blig bquery (Accepts := Accepts)
      (Fails := Fails) wrong_init budget_pair budget_round budget_in budget_lig budget_query
      right_of_accepts).doomed = (layerStepChainS steps Wrong init).doomed := rfl

/-- `layerStepRbrS`'s per-slot budget is the mixed budget. -/
theorem layerStepRbrS_beta [Fintype Cand] (steps : StepsS C S nl w)
    (Wrong : Cand → S → Prop) (init : S) (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init budget_pair budget_round budget_in budget_lig budget_query right_of_accepts) :
    (layerStepRbrS steps Wrong init bpair bround bin blig bquery (Accepts := Accepts)
      (Fails := Fails) wrong_init budget_pair budget_round budget_in budget_lig budget_query
      right_of_accepts).beta
      = fun i => mixedBudget (nl := nl) (w := w) (Fintype.card Cand) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i) := rfl

/--
**LayerStep, round by round, at the mixed budgets.**

```text
Pr[ accept ∧ fail ]  ≤  ( |Cand| · (nl·bpair + (∑ w)·bround + bin)  +  blig  +  bquery ) / |C|
```
-/
theorem layerStep_ratio_le_mixed [DecidableEq C] [Nonempty C] [Fintype Cand]
    (steps : StepsS C S nl w) (Wrong : Cand → S → Prop) (init : S)
    (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, Wrong cand init)
    (budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S),
      Wrong cand s → (univ.filter fun c : C => ¬ Wrong cand (steps.pair ly m pref c s)).card
        ≤ bpair)
    (budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.round ly j m pref c s)).card ≤ bround)
    (budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.inputBind m pref c s)).card ≤ bin)
    (budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroChallenge m pref c s)).card ≤ blig)
    (budget_query : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroQuery m pref c s)).card ≤ bquery)
    (right_of_accepts : ∀ tape : Fin (Rounds.Role.length nl w) → C, Accepts tape →
      ∃ cand : Cand, ¬ (layerStepChainS steps Wrong init).Wrong cand
        ((layerStepChainS steps Wrong init).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)))
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
            + blig + bquery : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  have h := (layerStepRbrS steps Wrong init bpair bround bin blig bquery (Accepts := Accepts)
    (Fails := Fails) wrong_init budget_pair budget_round budget_in budget_lig budget_query
    right_of_accepts).toCore.rbr_ratio_le hT
  have hsum : ∑ i, (layerStepRbrS steps Wrong init bpair bround bin blig bquery
      (Accepts := Accepts) (Fails := Fails) wrong_init budget_pair budget_round budget_in
      budget_lig budget_query right_of_accepts).toCore.beta i
      = Fintype.card Cand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
          + blig + bquery :=
    mixed_budget_sum (nl := nl) (w := w) _ _ _ _ _ _
  rwa [hsum] at h

/--
**LayerStep at the mixed budgets, summed over commitments.**  One `Bcs.Rbr` per commitment whose
per-slot budget is at most the mixed budget.
-/
theorem layerStep_ratio_le_mixed_prod {Pre : Type} [Fintype Pre] [Nonempty Pre]
    [DecidableEq C] [Nonempty C]
    {Acc : Pre × (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Pre → Prop}
    (R : ∀ pre : Pre, Bcs.Rbr C (Rounds.Role.length nl w)
      (fun tape => Acc (pre, tape)) (Fails pre))
    (cardCand bpair bround bin blig bquery : ℕ)
    (hb : ∀ (pre : Pre) (i : Fin (Rounds.Role.length nl w)), (R pre).beta i
      ≤ mixedBudget (nl := nl) (w := w) cardCand bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i))
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
        Acc omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((cardCand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin)
            + blig + bquery : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  refine Bcs.rbr_ratio_le_prod R _ (fun pre => ?_) hT
  calc ∑ i, (R pre).beta i
      ≤ ∑ i, mixedBudget (nl := nl) (w := w) cardCand bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i) := Finset.sum_le_sum (fun i _ => hb pre i)
    _ = _ := mixed_budget_sum (nl := nl) (w := w) _ _ _ _ _ _

end Chain

end Lfzk.RbrLayerStepS
