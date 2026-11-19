import TranscriptV2.SharedFailure
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The arbitrary-exception bound can be tight: one outcome is paid for by
an algebraic charge and another by the transcript exception. -/
namespace TranscriptV2.Tests.SharedFailure
open Finset
open scoped Classical

private abbrev failure (coin : Fin 4) : Prop := coin.val < 2
private abbrev exception (coin : Fin 4) : Prop := coin = 1
private abbrev charge (coin : Fin 4) : ℚ := if coin = 0 then 1 else 0

example : ((univ.filter failure).card : ℚ) / Fintype.card (Fin 4) ≤ 1/2 := by
  have bound := SharedFailure.failure_ratio_le failure exception charge
    (chargeBound := 1/4) (exceptionBound := 1/4)
    (by intro coin; fin_cases coin <;> norm_num [charge])
    (by intro coin; fin_cases coin <;> norm_num [failure, exception, charge])
    (by norm_num [charge, Fin.sum_univ_succ])
    (by norm_num [exception, card_filter, Fin.sum_univ_succ])
  convert bound using 1 <;> norm_num

-- Both contributions are needed: the displayed upper bound is attained.
example : ((univ.filter failure).card : ℚ) / Fintype.card (Fin 4) = 1/2 := by
  have events : univ.filter failure = ({0, 1} : Finset (Fin 4)) := by
    ext coin
    fin_cases coin <;> simp [failure]
  rw [events]
  norm_num

/--
info: 'TranscriptV2.SharedFailure.failure_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms SharedFailure.failure_ratio_le

end TranscriptV2.Tests.SharedFailure
