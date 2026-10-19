import polygero.Algebra.Counting.IntegerOccupancy

/-! Integer occupancy for sets of unequal sizes. The same coordinate
argument also constrains the sum of their sizes, information not retained
by independent cumulative tail bounds. -/
namespace CodingTheory.NonuniformOccupancy
open Finset
open scoped BigOperators

variable {D : Type} {n : ℕ}

private theorem sum_occurrences (T : Finset D) (sets : D → Finset (Fin n)) :
    (∑ j : Fin n, (T.filter fun d => j ∈ sets d).card) = ∑ d ∈ T, (sets d).card := by
  classical
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  exact sum_congr rfl fun d _ => by simp

private theorem sum_squares (T : Finset D) (sets : D → Finset (Fin n)) :
    (∑ j : Fin n, (T.filter fun d => j ∈ sets d).card ^ 2) =
      ∑ d ∈ T, ∑ e ∈ T, (sets d ∩ sets e).card := by
  classical
  have hcard (j : Fin n) : (T.filter fun d => j ∈ sets d).card =
      ∑ d ∈ T, if j ∈ sets d then 1 else 0 := by
    simp_rw [card_eq_sum_ones, sum_filter]
  simp_rw [hcard, pow_two, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  calc
    (∑ j, (if j ∈ sets d then 1 else 0) * (if j ∈ sets e then 1 else 0)) =
        ∑ j ∈ univ.filter (fun j => j ∈ sets d ∩ sets e), 1 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      by_cases hd : j ∈ sets d <;> by_cases he : j ∈ sets e <;> simp [hd, he]
    _ = (sets d ∩ sets e).card := by
      rw [show univ.filter (fun j => j ∈ sets d ∩ sets e) = sets d ∩ sets e by ext j; simp]
      simp

/-- Every indexed finite family, including unequal support sizes, obeys
the integer second-moment resource inequality. -/
theorem total_size {lam : ℕ} (T : Finset D) (sets : D → Finset (Fin n))
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (sets d ∩ sets e).card ≤ lam)
    (h : ℕ) :
    (2*h : ℤ) * ∑ d ∈ T, ((sets d).card : ℤ) ≤
      (T.card : ℤ) * (T.card-1) * lam + n*h*(h+1) := by
  classical
  by_cases hz : T = ∅
  · subst T
    simp only [card_empty, Nat.cast_zero, sum_empty, mul_zero, zero_mul, zero_add]
    positivity
  have hpos : 1 ≤ T.card := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr hz); omega
  let occ : Fin n → ℕ := fun j => (T.filter fun d => j ∈ sets d).card
  have hsum : (∑ j, occ j) = ∑ d ∈ T, (sets d).card := sum_occurrences T sets
  have hrow (d : D) (hd : d ∈ T) :
      (∑ e ∈ T, (sets d ∩ sets e).card) ≤ (sets d).card + (T.card-1)*lam := by
    calc
      _ ≤ ∑ e ∈ T, if e = d then (sets d).card else lam := by
        apply sum_le_sum
        intro e he
        by_cases hed : e = d
        · subst e; simp
        · simpa [hed] using hinter d hd e he (Ne.symm hed)
      _ = _ := by
        rw [← add_sum_erase T (fun e => if e = d then (sets d).card else lam) hd]
        rw [if_pos rfl]
        congr 1
        calc
          (∑ e ∈ T.erase d, if e = d then (sets d).card else lam) =
              ∑ _e ∈ T.erase d, lam := by
            apply sum_congr rfl
            intro e he
            rw [if_neg (ne_of_mem_erase he)]
          _ = _ := by simp [card_erase_of_mem hd]
  have hsquare : (∑ j, occ j ^ 2) ≤
      (∑ d ∈ T, (sets d).card) + T.card*(T.card-1)*lam := by
    rw [sum_squares]
    exact (sum_le_sum fun d hd => hrow d hd).trans_eq (by simp [sum_add_distrib, mul_assoc])
  have hsumZ : (∑ j, (occ j : ℤ)) = ∑ d ∈ T, ((sets d).card : ℤ) := by exact_mod_cast hsum
  have hsquareZ : (∑ j, (occ j : ℤ)^2) ≤
      (∑ d ∈ T, ((sets d).card : ℤ)) + (T.card : ℤ)*(T.card-1)*lam := by
    exact_mod_cast hsquare
  have hlow := sum_le_sum (s := (univ : Finset (Fin n)))
    (fun j _ => IntegerOccupancy.occupancy_gap (occ j) h)
  simp only [← mul_sum, sum_add_distrib, sum_sub_distrib, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, hsumZ] at hlow
  nlinarith

/-- An exact arithmetic certificate turns the resource inequality into
an integer bound on the total support size. -/
theorem sum_card_le {lam bound h : ℕ} (T : Finset D) (sets : D → Finset (Fin n))
    (hinter : ∀ d ∈ T, ∀ e ∈ T, d ≠ e → (sets d ∩ sets e).card ≤ lam)
    (hh : 0 < h)
    (hcert : (T.card : ℤ)*(T.card-1)*lam + n*h*(h+1) < (2*h : ℤ)*(bound+1)) :
    ∑ d ∈ T, (sets d).card ≤ bound := by
  have hi := total_size T sets hinter h
  by_contra hn
  have hlarge : bound+1 ≤ ∑ d ∈ T, (sets d).card := by omega
  have hlargeZ : (bound : ℤ)+1 ≤ ∑ d ∈ T, ((sets d).card : ℤ) := by exact_mod_cast hlarge
  have hhZ : 0 < (h : ℤ) := by exact_mod_cast hh
  nlinarith

end CodingTheory.NonuniformOccupancy
