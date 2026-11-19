import Bcs.FiniteProbability
import Mathlib.Tactic.Positivity

/-! Finite probability calculations shared by protocol reductions.
These lemmas have no transcript, field, verifier or sampler dependencies. -/
noncomputable section
namespace Bcs.FiniteProbability
open Finset
open scoped Classical

theorem density_le_one {Omega : Type} [Fintype Omega] [Nonempty Omega] (event : Omega → Prop) :
    density event ≤ 1 := by
  apply (density_mono (q := fun _ => True) (fun _ _ => trivial)).trans_eq
  simp [density,Fintype.card_ne_zero]

theorem density_le_mean {Omega : Type} [Fintype Omega] (event : Omega → Prop) (cost : Omega → ℚ)
    (nonnegative : ∀ x, 0 ≤ cost x) (paid : ∀ x, event x → 1 ≤ cost x) :
    density event ≤ (∑ x, cost x) / Fintype.card Omega := by
  unfold density
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ = ∑ x, if event x then (1 : ℚ) else 0 := by rw [← Finset.sum_filter]; simp
    _ ≤ _ := Finset.sum_le_sum fun x _ => by
      split_ifs with valid
      · exact paid x valid
      · exact nonnegative x

theorem mean_add_mul_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (first second : Omega → ℚ) (rate cap : ℚ) (bounded : ∀ x, first x + rate * second x ≤ cap) :
    (∑ x, first x) / Fintype.card Omega + rate * ((∑ x, second x) / Fintype.card Omega) ≤ cap := by
  rw [← mul_div_assoc,Finset.mul_sum,← add_div,← Finset.sum_add_distrib]
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm cap] using
    (Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => bounded x)

/-- A pointwise upper bound also bounds the uniform finite mean. -/
theorem mean_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (value : Omega → ℚ) (cap : ℚ) (bounded : ∀ x, value x ≤ cap) :
    (∑ x, value x) / Fintype.card Omega ≤ cap := by
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm cap] using
    (Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => bounded x)

/-- Averaging probabilities over any finite family of finite sample spaces
preserves the universal upper bound of one. -/
theorem mean_density_le_one {Omega : Type} [Fintype Omega] [Nonempty Omega]
    {Data : Omega → Type} [∀ x, Fintype (Data x)] [∀ x, Nonempty (Data x)]
    (event : (x : Omega) → Data x → Prop) :
    (∑ x, density (event x)) / Fintype.card Omega ≤ 1 :=
  mean_le _ 1 fun x => density_le_one (event x)

/-- Extend a useful small-budget estimate to every query budget when the
proposed upper bound is at least one beyond the cutoff. -/
theorem query_bound_or_one {probability bound : ℚ} (queries cutoff : ℕ)
    (probability_le_one : probability ≤ 1)
    (small : queries < cutoff → probability ≤ bound)
    (large : cutoff ≤ queries → 1 ≤ bound) : probability ≤ bound := by
  by_cases within : queries < cutoff
  · exact small within
  · exact probability_le_one.trans (large (Nat.le_of_not_gt within))

end Bcs.FiniteProbability
