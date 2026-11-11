import Bcs.FiniteProbability
import Mathlib.Tactic.Positivity

/-! Finite probability calculations shared by protocol reductions.
These lemmas have no transcript, field, verifier or sampler dependencies. -/
noncomputable section
namespace Bcs.FiniteProbability
open Finset
open scoped Classical

/-- A union of two oracle events spends the sum of their explicit error
bounds. Keep this finite-probability calculation independent of runtime types. -/
theorem event_union_le {Omega : Type} [Fintype Omega] (first second : Omega → Prop) :
    density (fun coin => first coin ∨ second coin) ≤ density first + density second := by
  have union := density_union_le (fun coin => first coin ∨ second coin)
    (fun flag : Bool => if flag then second else first) (by
      intro coin bad
      rcases bad with bad | bad
      · exact ⟨false,bad⟩
      · exact ⟨true,bad⟩)
  simpa only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true,add_comm] using union

theorem density_le_one {Omega : Type} [Fintype Omega] [Nonempty Omega] (event : Omega → Prop) :
    density event ≤ 1 := by
  apply (density_mono (q := fun _ => True) (fun _ _ => trivial)).trans_eq
  simp [density,Fintype.card_ne_zero]

/-- An expected number of queried addresses is the sum of their inclusion probabilities. -/
theorem mean_card {Omega P : Type} [Fintype Omega] [Fintype P] (points : Omega → Finset P) :
    (∑ h, ((points h).card : ℚ)) / Fintype.card Omega =
      ∑ p, density (fun h => p ∈ points h) := by
  simp only [density,← Finset.sum_div]
  congr 1
  have count := (Bcs.card_filter_prod_fst (fun x : Omega × P => x.2 ∈ points x.1)).symm.trans
    (Bcs.card_filter_prod_snd (fun x : Omega × P => x.2 ∈ points x.1))
  have fiber (h : Omega) : Finset.univ.filter (fun p => p ∈ points h) = points h := by
    ext p
    simp
  simp only [fiber] at count
  norm_cast
  refine count.trans (Finset.sum_congr rfl ?_)
  intro p _
  congr 1
  ext h
  simp

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

theorem density_add_mean_le {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (event : Omega → Prop) (cost budget auxiliary : Omega → ℚ) (rate cap : ℚ)
    (nonnegative : ∀ x, 0 ≤ cost x) (paid : ∀ x, event x → 1 ≤ cost x)
    (average : ∑ x, cost x ≤ ∑ x, budget x)
    (slots : ∀ x, budget x + rate * auxiliary x ≤ cap) :
    density event + rate * ((∑ x, auxiliary x) / Fintype.card Omega) ≤ cap :=
  (add_le_add ((density_le_mean event cost nonnegative paid).trans
    (div_le_div_of_nonneg_right average (Nat.cast_nonneg _))) le_rfl).trans
      (mean_add_mul_le budget auxiliary rate cap slots)

theorem density_shared_budget {Omega : Type} [Fintype Omega]
    (accepted failed recovered : Omega → Prop) {auxiliary cap correction : ℚ}
    (ordinary : density (fun h => (accepted h ∧ failed h) ∧ recovered h) + auxiliary ≤ cap)
    (hash : density (fun h => accepted h ∧ ¬recovered h) ≤ auxiliary + correction) :
    density (fun h => accepted h ∧ failed h) ≤ cap + correction := by
  have cover (h : Omega) (failure : accepted h ∧ failed h) :
      ((accepted h ∧ failed h) ∧ recovered h) ∨ (accepted h ∧ ¬recovered h) := by
    by_cases ready : recovered h
    · exact Or.inl ⟨failure,ready⟩
    · exact Or.inr ⟨failure.1,ready⟩
  have union := (density_mono cover).trans (event_union_le _ _)
  exact union.trans ((add_le_add le_rfl hash).trans
    ((add_assoc _ _ _).symm.le.trans (add_le_add ordinary le_rfl)))


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
