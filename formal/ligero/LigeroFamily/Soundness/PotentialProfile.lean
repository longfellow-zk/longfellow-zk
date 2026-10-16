import LigeroFamily.Soundness.AgreementProfile

/-!
# Finite agreement potentials

This file replaces a single good/bad agreement cutoff by a nondecreasing
rational potential.  Its layer-cake theorem applies to every agreement level,
including levels where only the trivial tail bound is known.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily.PotentialProfile

open Finset LigeroFamily.AgreementProfile
open scoped Classical

/-- A bounded monotone potential on the agreement interval. -/
structure Curve (n : ℕ) where
  value : ℕ → ℚ
  zero : value 0 = 0
  nonneg : ∀ a ≤ n, 0 ≤ value a
  le_one : ∀ a ≤ n, value a ≤ 1
  mono : ∀ a b, a ≤ b → b ≤ n → value a ≤ value b

/-- A finite positive mixture of agreement cutoffs.  Its weights may be
chosen by an untrusted optimizer; the three finite conditions are the
entire checked certificate for the curve itself. -/
def weightedStepCurve (n : ℕ) (steps : Finset ℕ) (weight : ℕ → ℚ)
    (hsteps : ∀ a ∈ steps, 0 < a)
    (hweight : ∀ a ∈ steps, 0 ≤ weight a)
    (htotal : ∑ a ∈ steps, weight a ≤ 1) : Curve n where
  value b := ∑ a ∈ steps, if a ≤ b then weight a else 0
  zero := by
    apply Finset.sum_eq_zero
    intro a ha
    simp only [show ¬ a ≤ 0 by have := hsteps a ha; omega, ↓reduceIte]
  nonneg := by
    intro b _
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact hweight a ha
    · exact le_refl _
  le_one := by
    intro b _
    apply le_trans _ htotal
    apply Finset.sum_le_sum
    intro a ha
    split_ifs
    · exact le_rfl
    · exact hweight a ha
  mono := by
    intro b c hbc _
    apply Finset.sum_le_sum
    intro a ha
    by_cases hab : a ≤ b
    · have hac : a ≤ c := hab.trans hbc
      simp only [if_pos hab, if_pos hac]
      exact le_refl _
    · by_cases hac : a ≤ c
      · simp only [if_neg hab, if_pos hac]
        exact hweight a ha
      · simp only [if_neg hab, if_neg hac]
        exact le_refl _

/-- The single-cutoff special case, useful when a side's contribution is
already negligible and grading does not improve the combined certificate. -/
def stepCurve (n a : ℕ) (ha : 0 < a) : Curve n :=
  weightedStepCurve n {a} (fun _ => 1)
    (by simpa using ha)
    (by simp)
    (by simp)

namespace Curve

variable {n : ℕ} (ψ : Curve n)

def increment (a : ℕ) : ℚ :=
  ψ.value a - if a = 0 then 0 else ψ.value (a - 1)

theorem increment_nonneg (a : ℕ) (ha : a ≤ n) : 0 ≤ ψ.increment a := by
  unfold increment
  by_cases hzero : a = 0
  · simp [hzero, ψ.zero]
  · simp only [hzero, ↓reduceIte]
    exact sub_nonneg.mpr (ψ.mono (a - 1) a (Nat.sub_le _ _) ha)

theorem sum_increment (a : ℕ) :
    ∑ i ∈ range (a + 1), ψ.increment i = ψ.value a := by
  induction a with
  | zero => simp [increment, ψ.zero]
  | succ a ih =>
      rw [sum_range_succ, ih]
      simp [increment]

theorem value_eq_tail_sum {X : Type*} (agreement : X → ℕ) (x : X)
    (h : agreement x ≤ n) :
    ψ.value (agreement x) =
      ∑ a ∈ range (n + 1),
        if a ≤ agreement x then ψ.increment a else 0 := by
  rw [← ψ.sum_increment (agreement x)]
  have hr : (range (n + 1)).filter (fun a => a ≤ agreement x) =
      range (agreement x + 1) := by
    ext a
    simp
    omega
  rw [← hr, sum_filter]

/-- Exact layer-cake accounting for an arbitrary monotone potential.  The
tail bound may be clipped at one independently at each agreement level. -/
theorem mean_le_tail_sum {X : Type*} [Fintype X] [Nonempty X]
    (agreement : X → ℕ) (hagreement : ∀ x, agreement x ≤ n)
    (tail : ℕ → ℚ)
    (htail : ∀ a ≤ n,
      ((tailSet agreement a).card : ℚ) / Fintype.card X ≤ tail a) :
    (∑ x : X, ψ.value (agreement x)) / Fintype.card X ≤
      ∑ a ∈ range (n + 1), ψ.increment a * tail a := by
  classical
  have hsum :
      (∑ x : X, ψ.value (agreement x)) =
        ∑ a ∈ range (n + 1),
          ψ.increment a * (tailSet agreement a).card := by
    calc
      (∑ x : X, ψ.value (agreement x)) =
          ∑ x : X, ∑ a ∈ range (n + 1),
            if a ≤ agreement x then ψ.increment a else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        exact ψ.value_eq_tail_sum agreement x (hagreement x)
      _ = ∑ a ∈ range (n + 1), ∑ x : X,
            if a ≤ agreement x then ψ.increment a else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_filter]
        simp [tailSet, mul_comm]
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a ha
  have han : a ≤ n := by
    have := Finset.mem_range.mp ha
    omega
  calc
    (ψ.increment a * (tailSet agreement a).card) *
        (Fintype.card X : ℚ)⁻¹ =
      ψ.increment a *
        ((tailSet agreement a).card / Fintype.card X) := by
          rw [div_eq_mul_inv]
          ring
    _ ≤ ψ.increment a * tail a :=
      mul_le_mul_of_nonneg_left (htail a han) (ψ.increment_nonneg a han)

/-- The charge for one fresh query after the combination challenge. -/
def queryCost (cover : ℕ → ℚ) : ℚ :=
  (range (n + 1)).sup' (by simp) fun a => (1 - ψ.value a) * cover a

end Curve

end LigeroFamily.PotentialProfile
