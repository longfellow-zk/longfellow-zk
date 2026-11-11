import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Positivity

/-! Averaging a shared algebraic charge with an arbitrary transcript exception.
The query-counting and local algebraic budgets are independent of the syntax
used to establish the accepted path. A new chain construction supplies only
its path-charge cover and its separately proved exception probability. -/
namespace TranscriptV2.SharedFailure
open Finset
open scoped Classical

/-- Keep the algebraic charge and chain exception separate until their final
sum. In particular, verifier replay belongs in the exception bound rather
than increasing the adversarial budget in the algebraic term. -/
theorem failure_ratio_le {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (failure exception : Ω → Prop) (charge : Ω → ℚ)
    {chargeBound exceptionBound : ℚ}
    (nonneg : ∀ coin, 0 ≤ charge coin)
    (cover : ∀ coin, failure coin → ¬exception coin → 1 ≤ charge coin)
    (average : (∑ coin, charge coin) ≤ chargeBound * Fintype.card Ω)
    (exceptionRatio : ((univ.filter exception).card : ℚ) / Fintype.card Ω ≤ exceptionBound) :
    ((univ.filter failure).card : ℚ) / Fintype.card Ω ≤ chargeBound + exceptionBound := by
  have pointwise (coin : Ω) :
      (if failure coin then (1 : ℚ) else 0) ≤
        (if exception coin then 1 else 0) + charge coin := by
    by_cases hf : failure coin
    · by_cases he : exception coin
      · simpa only [if_pos hf, if_pos he] using le_add_of_nonneg_right (nonneg coin)
      · simpa only [if_pos hf, if_neg he, zero_add] using cover coin hf he
    · simp only [if_neg hf]
      exact add_nonneg (by split_ifs <;> norm_num) (nonneg coin)
  have count : ((univ.filter failure).card : ℚ) ≤
      (univ.filter exception).card + ∑ coin, charge coin := by
    simpa [sum_add_distrib] using sum_le_sum (fun coin (_ : coin ∈ univ) => pointwise coin)
  have positive : (0 : ℚ) < Fintype.card Ω := by positivity
  have chargeRatio : (∑ coin, charge coin) / Fintype.card Ω ≤ chargeBound :=
    (div_le_iff₀ positive).mpr average
  have combined := div_le_div_of_nonneg_right count positive.le
  rw [add_div] at combined
  exact combined.trans ((add_le_add exceptionRatio chargeRatio).trans_eq (add_comm _ _))

end TranscriptV2.SharedFailure
