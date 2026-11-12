import JBAgreement.Counting
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Sharp degree-weighted factor selection

The Newton-skeleton ledger assigns a factor of original `Y`-degree `r` and
`Z`-height `h` the capacity `4 * k * (r * h) + r`.  Summing the exact capacities
before applying the global degree and height bounds gives
`4 * k * (dY * dZ) + dY`.
-/

namespace JBAgreement

open Finset
open scoped BigOperators

/-- The sharp Newton-skeleton capacity.  A common clearing exponent `2 * κ` gives
`T`-degree at most `2κd` and `Z`-height at most `2κh`; intersecting with a fiber
factor of bidegree `(dH,hH)` gives this rectangle. -/
def sharpFiberCapacity (κ d h N dH hH : ℕ) : ℕ :=
  (2 * κ * d) * hH + dH * (2 * κ * h + N)

/-- Sharp fiber capacities add before applying the factor's degree and height bounds. -/
theorem sum_sharpFiberCapacity_le {β : Type*} [DecidableEq β] (P : Finset β)
    (degree height : β → ℕ) {κ d h N : ℕ}
    (hdegree : ∑ b ∈ P, degree b ≤ d) (hheight : ∑ b ∈ P, height b ≤ h) :
    ∑ b ∈ P, sharpFiberCapacity κ d h N (degree b) (height b) ≤
      4 * κ * (d * h) + d * N := by
  have h₁ : (2 * κ * d) * (∑ b ∈ P, height b) ≤ (2 * κ * d) * h :=
    Nat.mul_le_mul_left _ hheight
  have h₂ : (∑ b ∈ P, degree b) * (2 * κ * h + N) ≤
      d * (2 * κ * h + N) := Nat.mul_le_mul_right _ hdegree
  calc
    ∑ b ∈ P, sharpFiberCapacity κ d h N (degree b) (height b) =
        (2 * κ * d) * (∑ b ∈ P, height b) +
          (∑ b ∈ P, degree b) * (2 * κ * h + N) := by
            simp_rw [sharpFiberCapacity]
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ (2 * κ * d) * h + d * (2 * κ * h + N) := Nat.add_le_add h₁ h₂
    _ = 4 * κ * (d * h) + d * N := by ring

/-- The Frobenius cancellation in natural-number form.  If the separable factor has
degree `d`, the original factor has degree `r = d*N`, and the jet order is `k*N`, then
the sharp capacity is charged only once to `r`. -/
theorem sharp_extractedCapacity_le {k d h N r : ℕ} (hr : d * N = r) :
    4 * (k * N) * (d * h) + d * N ≤ 4 * k * (r * h) + r := by
  subst r
  ring_nf
  exact le_rfl

/-- The total sharp algebraic capacity assigned to an original factor. -/
def sharpFactorCapacity (k h r : ℕ) : ℕ := 4 * k * (r * h) + r

/-- Summing sharp capacities over factors uses their exact individual `Z`-heights.
This is the algebraic source of `4*k*dY*dZ + dY`. -/
theorem sum_sharpFactorCapacity_le {β : Type*} [DecidableEq β] (P : Finset β)
    (degree height : β → ℕ) {k dY dZ : ℕ}
    (hdegree : ∑ b ∈ P, degree b ≤ dY)
    (hheight : ∑ b ∈ P, height b ≤ dZ) :
    ∑ b ∈ P, sharpFactorCapacity k (height b) (degree b) ≤
      4 * k * (dY * dZ) + dY := by
  have hcross : ∑ b ∈ P, degree b * height b ≤ dY * dZ := by
    calc
      ∑ b ∈ P, degree b * height b
          ≤ (∑ b ∈ P, degree b) * (∑ b ∈ P, height b) := by
            rw [Finset.sum_mul_sum]
            exact Finset.sum_le_sum fun b hb =>
              Finset.single_le_sum (fun j _ => Nat.zero_le (degree b * height j)) hb
      _ ≤ dY * dZ := Nat.mul_le_mul hdegree hheight
  calc
    ∑ b ∈ P, sharpFactorCapacity k (height b) (degree b) =
        4 * k * (∑ b ∈ P, degree b * height b) + ∑ b ∈ P, degree b := by
          simp_rw [sharpFactorCapacity]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 4 * k * (dY * dZ) + dY :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hcross) hdegree

/-- Uniform-height specialization used when each extracted branch inherits the same
global `Z`-height bound, while the original branch degrees still add to `dY`. -/
theorem sum_sharpFactorCapacity_uniform_height_le {β : Type*} [DecidableEq β]
    (P : Finset β) (degree : β → ℕ) {k dY dZ : ℕ}
    (hdegree : ∑ b ∈ P, degree b ≤ dY) :
    ∑ b ∈ P, sharpFactorCapacity k dZ (degree b) ≤
      4 * k * (dY * dZ) + dY := by
  calc
    ∑ b ∈ P, sharpFactorCapacity k dZ (degree b) =
        (4 * k * dZ + 1) * ∑ b ∈ P, degree b := by
          simp_rw [sharpFactorCapacity]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ ≤ (4 * k * dZ + 1) * dY := Nat.mul_le_mul_left _ hdegree
    _ = 4 * k * (dY * dZ) + dY := by ring

/-- Finite sums of natural-number quotients are bounded by the quotient of the sum. -/
theorem sum_div_le_div_sum {β : Type*} [DecidableEq β] (P : Finset β)
    (f : β → ℕ) (s : ℕ) :
    (∑ b ∈ P, f b / s) ≤ (∑ b ∈ P, f b) / s := by
  induction P using Finset.induction with
  | empty => simp
  | @insert b P hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact (Nat.add_le_add_left ih _).trans (Nat.add_div_le_add_div _ _ _)

/-- Per-label bucket threshold, combining the minimum useful bucket size with the
incidence quotient for that label's exact capacity. -/
def incidenceThreshold (n slack e capacity : ℕ) : ℕ :=
  e + 2 + n * capacity / slack

theorem incidenceThreshold_min (n slack e capacity : ℕ) :
    e + 1 ≤ incidenceThreshold n slack e capacity := by
  unfold incidenceThreshold
  exact (show e + 1 ≤ e + 2 by omega).trans (Nat.le_add_right _ _)

theorem incidenceThreshold_incidence {n slack e capacity : ℕ} (hslack : 0 < slack) :
    n * capacity < slack * incidenceThreshold n slack e capacity := by
  have hq := Nat.lt_mul_div_succ (n * capacity) hslack
  have hle : n * capacity / slack + 1 ≤ incidenceThreshold n slack e capacity := by
    unfold incidenceThreshold
    omega
  exact hq.trans_le (Nat.mul_le_mul_left slack hle)

/-- Closed bound for the sum of all per-label incidence thresholds. -/
theorem sum_incidenceThreshold_le {β : Type*} [DecidableEq β] (P : Finset β)
    (capacity : β → ℕ) (n slack e : ℕ) :
    (∑ b ∈ P, incidenceThreshold n slack e (capacity b)) ≤
      P.card * (e + 2) + n * (∑ b ∈ P, capacity b) / slack := by
  have hdiv := sum_div_le_div_sum P (fun b => n * capacity b) slack
  calc
    ∑ b ∈ P, incidenceThreshold n slack e (capacity b) =
        P.card * (e + 2) + ∑ b ∈ P, n * capacity b / slack := by
      simp [incidenceThreshold, Finset.sum_add_distrib]
    _ ≤ P.card * (e + 2) + (∑ b ∈ P, n * capacity b) / slack :=
      Nat.add_le_add_left hdiv _
    _ = P.card * (e + 2) + n * (∑ b ∈ P, capacity b) / slack := by
      rw [Finset.mul_sum]

/-- Weighted pigeonhole: some fiber is larger than its assigned capacity whenever the
sum of capacities is smaller than the source set. -/
theorem exists_weighted_bucket {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (label : α → β) (P : Finset β) (weight : β → ℕ)
    (hlabel : ∀ x ∈ S, label x ∈ P)
    (hweight : (∑ b ∈ P, weight b) < S.card) :
    ∃ b ∈ P, weight b < (S.filter fun x => label x = b).card := by
  classical
  by_contra h
  have hle : ∀ b ∈ P, (S.filter fun x => label x = b).card ≤ weight b := by
    intro b hb
    exact Nat.le_of_not_gt (fun hgt => h ⟨b, hb, hgt⟩)
  have hcard : S.card = ∑ b ∈ P, (S.filter fun x => label x = b).card := by
    calc
      S.card = ∑ x ∈ S, 1 := by simp
      _ = ∑ x ∈ S, ∑ b ∈ P, if label x = b then 1 else 0 := by
        refine Finset.sum_congr rfl fun x hx => ?_
        simp [hlabel x hx]
      _ = ∑ b ∈ P, ∑ x ∈ S, if label x = b then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ b ∈ P, (S.filter fun x => label x = b).card := by
        refine Finset.sum_congr rfl fun b _ => ?_
        exact (Finset.card_filter (fun x => label x = b) S).symm
  have := Finset.sum_le_sum fun b hb => hle b hb
  rw [← hcard] at this
  exact (not_le_of_gt hweight) this

/-- Weighted selection in the form required by the branch-incidence argument.  The
per-factor threshold simultaneously dominates `e + 1` and is large enough for that
factor's individual column bound. -/
theorem exists_weighted_incidence_bucket {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (label : α → β) (P : Finset β)
    (capacity threshold : β → ℕ) {n slack e : ℕ}
    (hlabel : ∀ x ∈ S, label x ∈ P) (hslack : 1 ≤ slack)
    (hmin : ∀ b ∈ P, e + 1 ≤ threshold b)
    (hinc : ∀ b ∈ P, n * capacity b < slack * threshold b)
    (hsum : (∑ b ∈ P, threshold b) < S.card) :
    ∃ b ∈ P,
      e + 1 < (S.filter fun x => label x = b).card ∧
        n * capacity b < slack * (S.filter fun x => label x = b).card := by
  obtain ⟨b, hb, hbucket⟩ := exists_weighted_bucket S label P threshold hlabel hsum
  refine ⟨b, hb, (hmin b hb).trans_lt hbucket, (hinc b hb).trans ?_⟩
  exact Nat.mul_lt_mul_of_pos_left hbucket hslack

end JBAgreement
