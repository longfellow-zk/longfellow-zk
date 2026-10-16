import Lfzk.RbrZkFlat

/-!
# Local graded terminal data for the Longfellow chain

The combination challenge receives a bounded rational weight determined by
the built system and decoded challenge.  The column query receives the
residual weight if it passes.  Both local bounds are exact sums over hash
answers.  A field-round escape remains a unit charge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit
open scoped Classical

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F]
  [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {M ninp logw logc : ℕ}
variable [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q]
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {asg : Lift → LigeroAssignment ninp M F}

/-- The local obligations for an exact, unthresholded split of Ligero's
combination challenge and column query.  `weight` is fixed by the built
system and decoded combination challenge, so the query's residual weight
does not depend on the fresh query answer. -/
structure TerminalPotential (LD : ZkLigeroData C X Q Msg V asg) where
  weight : LigeroSystem ninp M F → X → ℚ
  nonneg : ∀ sys x, 0 ≤ weight sys x
  le_one : ∀ sys x, weight sys x ≤ 1
  challengeBudget : ℚ
  queryBudget : ℚ
  challengeBudget_nonneg : 0 ≤ challengeBudget
  queryBudget_nonneg : 0 ≤ queryBudget
  challenge_le : ∀ sys, Fits V sys → NoSat asg sys →
    (∑ c : C, weight sys (V.decodeChal c)) ≤ challengeBudget
  query_le : ∀ (m : ℕ) (pref : Fin m → C) (msg : Msg)
      (sys : LigeroSystem ninp M F) (x : X),
    Fits V sys → NoSat asg sys →
    (∑ c : C, if V.decodeQuery c ∈ LD.accepting m pref msg sys x then
      1 - weight sys x else 0) ≤ queryBudget

/-- A coarse potential used when a terminal event is counted directly.
Its terminal budgets are deliberately weak; after removing the terminal
slots from the hybrid charge, neither budget enters the FS estimate. -/
noncomputable def TerminalPotential.coarse
    (LD : ZkLigeroData C X Q Msg V asg) : TerminalPotential LD where
  weight := fun _ _ => 0
  nonneg := by intros; exact le_refl _
  le_one := by intros; norm_num
  challengeBudget := 0
  queryBudget := Fintype.card C
  challengeBudget_nonneg := le_refl _
  queryBudget_nonneg := by positivity
  challenge_le := by intros; simp
  query_le := by
    intro m pref msg sys x _ _
    simp only [sub_zero]
    have hcard := Finset.card_filter_le (Finset.univ : Finset C)
      (fun c => V.decodeQuery c ∈ LD.accepting m pref msg sys x)
    have hcardq :
        ((Finset.univ.filter fun c : C =>
          V.decodeQuery c ∈ LD.accepting m pref msg sys x).card : ℚ) ≤
          Fintype.card C := by
      exact_mod_cast hcard
    simpa only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] using
      hcardq

end Lfzk.RbrZkFlat
