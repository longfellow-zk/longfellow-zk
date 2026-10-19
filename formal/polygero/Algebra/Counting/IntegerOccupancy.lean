import CodingTheory.ListDecoding.UniformFamily
import Mathlib.Tactic.Linarith

/-! An integer refinement of the second-moment uniform-family bound.
For each integer column occupancy m, (m-h)(m-h-1) is nonnegative.
Unlike Cauchy--Schwarz, this retains the gap between consecutive integers.
No algebraic property of a particular code is assumed. -/
namespace CodingTheory.IntegerOccupancy
open Finset
open scoped BigOperators

private theorem sum_occurrences {n : ℕ} (family : Finset (Finset (Fin n))) :
    (∑ j : Fin n, (family.filter fun A => j ∈ A).card) = ∑ A ∈ family, A.card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun A _ => by simp

private theorem sum_squares {n : ℕ} (family : Finset (Finset (Fin n))) :
    (∑ j : Fin n, (family.filter fun A => j ∈ A).card ^ 2) =
      ∑ A ∈ family, ∑ B ∈ family, (A ∩ B).card := by
  have hcard (j : Fin n) : (family.filter fun A => j ∈ A).card =
      ∑ A ∈ family, if j ∈ A then 1 else 0 := by
    simp_rw [card_eq_sum_ones, sum_filter]
  simp_rw [hcard, pow_two, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro A _
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro B _
  calc
    (∑ j, (if j ∈ A then 1 else 0) * (if j ∈ B then 1 else 0)) =
        ∑ j ∈ univ.filter (fun j => j ∈ A ∩ B), 1 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      by_cases ha : j ∈ A <;> by_cases hb : j ∈ B <;> simp [ha, hb]
    _ = (A ∩ B).card := by
      rw [show univ.filter (fun j => j ∈ A ∩ B) = A ∩ B by ext j; simp]
      simp

/-- Every integer occupancy lies outside the open interval (h,h+1). -/
theorem occupancy_gap (m h : ℕ) :
    (2 * h : ℤ) * m ≤ (m : ℤ)^2 - m + (h : ℤ) * (h + 1) := by
  by_cases hh : m ≤ h
  · have hm : (m : ℤ) ≤ h := by exact_mod_cast hh
    have hp := mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hm) (show (m : ℤ) - h - 1 ≤ 0 by omega)
    nlinarith
  · have hm : (h : ℤ) + 1 ≤ m := by exact_mod_cast (show h + 1 ≤ m by omega)
    have hp := mul_nonneg (show 0 ≤ (m : ℤ) - h by omega)
      (show 0 ≤ (m : ℤ) - h - 1 by omega)
    nlinarith

/-- Integer second-moment inequality for an actual uniform family. -/
theorem family_inequality {n w lam : ℕ} (family : Finset (Finset (Fin n)))
    (hcard : ∀ A ∈ family, A.card = w)
    (hinter : ∀ A ∈ family, ∀ B ∈ family, A ≠ B → (A ∩ B).card ≤ lam)
    (h : ℕ) :
    (2 * h : ℤ) * family.card * w ≤
      (family.card : ℤ) * (family.card - 1) * lam + n * h * (h + 1) := by
  classical
  by_cases hz : family = ∅
  · subst family
    simp only [card_empty, Nat.cast_zero, mul_zero, zero_mul, zero_add]
    positivity
  have hpos : 1 ≤ family.card := by
    have := card_pos.mpr (nonempty_iff_ne_empty.mpr hz)
    omega
  let occ : Fin n → ℕ := fun j => (family.filter fun A => j ∈ A).card
  have hsum : (∑ j, occ j) = family.card * w := by
    rw [sum_occurrences]
    exact (sum_congr rfl fun A ha => hcard A ha).trans (by simp)
  have hrow (A : Finset (Fin n)) (ha : A ∈ family) :
      (∑ B ∈ family, (A ∩ B).card) ≤ w + (family.card - 1) * lam := by
    calc
      _ ≤ ∑ B ∈ family, if B = A then w else lam := by
        apply sum_le_sum
        intro B hb
        by_cases he : B = A
        · subst B; simp [hcard A ha]
        · simpa [he] using hinter A ha B hb (Ne.symm he)
      _ = _ := by
        rw [← add_sum_erase family (fun B => if B = A then w else lam) ha]
        rw [if_pos rfl]
        congr 1
        calc
          (∑ B ∈ family.erase A, if B = A then w else lam) =
              ∑ _B ∈ family.erase A, lam := by
            apply sum_congr rfl
            intro B hb
            rw [if_neg (ne_of_mem_erase hb)]
          _ = _ := by simp [card_erase_of_mem ha]
  have hsquare : (∑ j, occ j ^ 2) ≤ family.card * (w + (family.card - 1) * lam) := by
    rw [sum_squares]
    exact (sum_le_sum fun A ha => hrow A ha).trans_eq (by simp)
  have hsumZ : (∑ j, (occ j : ℤ)) = (family.card : ℤ) * w := by
    exact_mod_cast hsum
  have hsquareZ : (∑ j, (occ j : ℤ)^2) ≤
      (family.card : ℤ) * (w + (family.card - 1) * lam) := by
    exact_mod_cast hsquare
  have hlow := sum_le_sum (s := (univ : Finset (Fin n)))
    (fun j _ => occupancy_gap (occ j) h)
  simp only [← mul_sum, sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, hsumZ] at hlow
  nlinarith

/-- Forbid an exact (L+1)-member subfamily using an integer occupancy h.
This is a directly usable replacement for a Johnson/Hahn list certificate. -/
theorem uniformFamilyBound {n w lam L h : ℕ}
    (hgap : (L + 1 : ℤ) * L * lam + n * h * (h + 1) <
      2 * h * (L + 1) * w) : CodingTheory.UniformFamilyBound n w lam L := by
  classical
  intro family hcard hinter
  by_contra hn
  obtain ⟨sub, hsub, hsize⟩ := exists_subset_card_eq
    (show L + 1 ≤ family.card by omega)
  have hi := family_inequality sub (fun A ha => hcard A (hsub ha))
    (fun A ha B hb hne => hinter A (hsub ha) B (hsub hb) hne) h
  rw [hsize] at hi
  push_cast at hi
  nlinarith

end CodingTheory.IntegerOccupancy
