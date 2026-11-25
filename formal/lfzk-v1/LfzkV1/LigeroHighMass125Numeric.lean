import LfzkV1.LigeroHighMass125Joint

/-!
# Finite upper envelope for the hash-side high coefficient

Below the sharp three-radius boundary the outer line count suffices.
Above it, each unit of the three-radius tail contributes one binomial
prefix sum. This gives a small kernel-checkable sum of binomial counts.
Only the multiplicity correction uses the sharper local count, and only
at the high-agreement cutoff.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile
open scoped Classical

private theorem cover_eq (n r b : ℕ) (hb : b ≤ n) :
    coverRatio n n 0 r b = hypergeometricRatio b n r := by
  simp [coverRatio, min_eq_right hb]

private theorem tail_below {q n e g d outer a x : ℕ} {localBound : ℕ → ℕ}
    (hq : g + 1 < q) (hd : 0 < d) (ha : a ≤ n) (hx : x ≤ n)
    (houter : 1 + (d - 1) / 3 / (g + 1) ≤ outer) :
    (let profile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d
      outer localBound
     profile.tail (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator q g) (max a x)) ≤
      (if x ≤ n - (d - 1) / 3 - 1 then outer
        else 1 + (n - x) / (g + 1) : ℕ) / ((q - (g+1) : ℕ) : ℚ) := by
  let b := max a x
  let limit := if x ≤ n - (d - 1) / 3 - 1 then outer else 1 + (n - x) / (g + 1)
  have hb : b ≤ n := max_le ha hx
  have hlabelOuter : (SchemeSelectedMCA.selectedMCAFailureProfile n g d outer).labelsAtLeast b ≤ limit := by
    unfold SchemeSelectedMCA.selectedMCAFailureProfile
    simp only [show ¬n < b by omega, ↓reduceIte]
    by_cases hsharp : 3 * (n - b) < d
    · rw [if_pos hsharp]
      have hdiv : n - b ≤ (d - 1) / 3 := by omega
      unfold limit
      split
      · exact (Nat.add_le_add_left (Nat.div_le_div_right hdiv) 1).trans houter
      · have hb' : x ≤ b := le_max_right _ _
        exact Nat.add_le_add_left (Nat.div_le_div_right (Nat.sub_le_sub_left hb' n)) 1
    · rw [if_neg hsharp]
      have hx' : x ≤ b := le_max_right _ _
      have hnot : x ≤ n - (d - 1) / 3 - 1 := by omega
      simp [limit, hnot]
  have hlabelIntegrated :
      (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d outer localBound).labelsAtLeast b ≤ limit := by
    unfold SchemeSelectedMCA.selectedMCAIntegratedFailureProfile
    dsimp only
    split
    · exact (min_le_left _ _).trans hlabelOuter
    · exact hlabelOuter
  have hlabel :
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d
        outer localBound).labelsAtLeast b ≤ q * limit := by
    unfold SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
      SchemeSelectedMCA.endpointOptimizedProfile
    dsimp only
    split
    · exact (min_le_left _ _).trans (Nat.mul_le_mul_left _ hlabelIntegrated)
    · exact Nat.mul_le_mul_left _ hlabelIntegrated
  let s := q - (g + 1)
  have hq' : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hs : (0 : ℚ) < s := by exact_mod_cast Nat.sub_pos_of_lt hq
  dsimp only
  unfold tail SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
  apply (min_le_right _ _).trans
  calc
    _ ≤ ((q * limit : ℕ) : ℚ) / ((q * s : ℕ) : ℚ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hlabel) (by positivity)
    _ = _ := by
      change ((q * limit : ℕ) : ℚ) / ((q * s : ℕ) : ℚ) = (limit : ℚ) / (s : ℚ)
      push_cast
      field_simp

/-- Kernel-friendly integer count for the contribution of the selected peak. -/
def noLiftPeakNumerator (n r d g outer : ℕ) : ℕ :=
  outer * (n - (d - 1) / 3 - 1).choose r + n.choose r +
    ∑ i ∈ range ((d - 1) / 3 / (g + 1)), (n - (i + 1) * (g + 1)).choose r

private theorem noLift_peak_bound {q n e g d r a outer : ℕ} {localBound : ℕ → ℕ}
    (hq : g + 1 < q) (hd : 0 < d) (ha : a ≤ n)
    (houter : 1 + (d - 1) / 3 / (g + 1) ≤ outer) :
    let profile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d
      outer localBound
    (truncateBelow profile a).contribution
      (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator q g) n n 0 r ≤
      (noLiftPeakNumerator n r d g outer : ℚ) / ((n.choose r * (q - (g+1)) : ℕ) : ℚ) := by
  classical
  dsimp only
  let s := q - (g + 1)
  let b := n - (d - 1) / 3 - 1
  let T := (d - 1) / 3 / (g + 1)
  let top (i : ℕ) := n - (i + 1) * (g + 1)
  let weight (x : ℕ) := (if x ≤ b then (outer : ℚ) else 0) + 1 +
    ∑ i ∈ range T, if x ≤ top i then (1 : ℚ) else 0
  have hweight (x : ℕ) (hx : x ≤ n) :
      ((if x ≤ b then outer else 1 + (n - x) / (g + 1) : ℕ) : ℚ) ≤ weight x := by
    by_cases hxb : x ≤ b
    · simp only [hxb, ↓reduceIte, weight]
      have hnonneg : 0 ≤ ∑ i ∈ range T, if x ≤ top i then (1 : ℚ) else 0 :=
        sum_nonneg fun i _ => by split <;> positivity
      linarith
    · have hclose : n - x ≤ (d - 1) / 3 := by dsimp [b] at hxb; omega
      have hT : (n - x) / (g + 1) ≤ T := Nat.div_le_div_right hclose
      have hsub : range ((n - x) / (g + 1)) ⊆ (range T).filter (fun i => x ≤ top i) := by
        intro i hi
        have hi' := mem_range.mp hi
        have hmul : (i + 1) * (g + 1) ≤ n - x :=
          (Nat.le_div_iff_mul_le (by omega : 0 < g + 1)).mp (by omega)
        exact mem_filter.mpr ⟨mem_range.mpr (hi'.trans_le hT), by dsimp [top]; omega⟩
      have hcard := card_le_card hsub
      rw [card_range] at hcard
      have hsum : ((n - x) / (g + 1) : ℕ) ≤
          ((range T).filter (fun i => x ≤ top i)).card := hcard
      simp only [hxb, ↓reduceIte, weight, zero_add, Nat.cast_add, Nat.cast_one]
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      exact add_le_add le_rfl (by exact_mod_cast hsum)
  let Δ := coverIncrement n n 0 r
  have htail (x : ℕ) (hx : x ≤ n) :
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d outer localBound).tail
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator q g) (max a x) ≤ weight x / s := by
    exact (tail_below (e := e) (localBound := localBound) hq hd ha hx houter).trans
      (div_le_div_of_nonneg_right (hweight x hx) (by positivity))
  have hpref (t : ℕ) (ht : t ≤ n) :
      (∑ x ∈ range (n+1), if x ≤ t then Δ x else 0) = hypergeometricRatio t n r := by
    rw [sum_coverIncrement_if_le, min_eq_right ht, cover_eq n r t ht]
  have hsum :
      ∑ x ∈ range (n+1), Δ x * weight x =
        (outer : ℚ) * hypergeometricRatio b n r + hypergeometricRatio n n r +
          ∑ i ∈ range T, hypergeometricRatio (top i) n r := by
    have hf (t : ℕ) (ht : t ≤ n) (c : ℚ) :
        (∑ x ∈ range (n+1), Δ x * (if x ≤ t then c else 0)) =
          c * hypergeometricRatio t n r := by
      rw [← hpref t ht, mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases h : x ≤ t <;> simp [h, mul_comm]
    simp only [weight, mul_add, sum_add_distrib, mul_one, mul_sum]
    rw [hf b (by dsimp [b]; omega), sum_coverIncrement, cover_eq n r n le_rfl]
    congr 1
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    simpa using hf (top i) (Nat.sub_le _ _) 1
  unfold contribution
  calc
    _ ≤ ∑ x ∈ range (n+1), Δ x * (weight x / s) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (htail x (by simpa using mem_range.mp hx))
        (coverIncrement_nonnegative _ _ _ _ _)
    _ = (∑ x ∈ range (n+1), Δ x * weight x) / s := by
      simp only [div_eq_mul_inv, sum_mul, mul_assoc]
    _ = _ := by
      rw [hsum]
      unfold hypergeometricRatio noLiftPeakNumerator
      push_cast
      change (outer * (↑(b.choose r) / ↑(n.choose r)) + ↑(n.choose r) / ↑(n.choose r) +
        (∑ i ∈ range T, ((top i).choose r : ℚ) / (n.choose r : ℚ))) / (s : ℚ) =
        (↑outer * ↑(b.choose r) + ↑(n.choose r) + ∑ i ∈ range T, ↑((top i).choose r)) /
          (↑(n.choose r) * (s : ℚ))
      have hdiv : (∑ i ∈ range T, ↑((top i).choose r) / (n.choose r : ℚ)) =
          (∑ i ∈ range T, (↑((top i).choose r) : ℚ)) / (n.choose r : ℚ) := by
        simp only [div_eq_mul_inv, sum_mul]
      rw [hdiv]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Put the four contributions over one common denominator. This representation
keeps the finite coefficient check entirely in natural arithmetic. -/
def highMassNumerator (q n k d g r a L outer : ℕ) (profile : AgreementProfile n) : ℕ :=
  let s := q - (g + 1)
  q * noLiftPeakNumerator n r d g outer +
    L * ((n + (2 * k - 1)) / 2).choose r * profile.labelsAtLeast a +
    s * (n.choose r + ((n + (n - d)) / 2 + g).choose r +
      2 * L * ((n + (2 * k - 1) + g) / 2).choose r)

theorem highMass_le_of_numerator_bound {q n k e d g r a L outer : ℕ} {localBound : ℕ → ℕ}
    (hq : g + 1 < q) (hd : 0 < d) (ha : a ≤ n) (hr : r ≤ n)
    (houter : 1 + (d - 1) / 3 / (g + 1) ≤ outer)
    (hcheck : 100 * highMassNumerator q n k d g r a L outer
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d outer localBound) ≤
      319 * n.choose r * (q - (g + 1))) :
    highMassBound q n k d g r a L (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator q g)
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d outer localBound) ≤
      (319 : ℚ) / (100 * q) := by
  let s := q - (g + 1)
  let m := n.choose r
  let profile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile q n e g d
    outer localBound
  let mid := ((n + (2 * k - 1)) / 2).choose r
  let second := ((n + (n - d)) / 2 + g).choose r
  let other := ((n + (2 * k - 1) + g) / 2).choose r
  let num := highMassNumerator q n k d g r a L outer profile
  have hs : (0 : ℚ) < s := by exact_mod_cast Nat.sub_pos_of_lt hq
  have hq' : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
  have hm : (0 : ℚ) < m := by exact_mod_cast Nat.choose_pos hr
  have hmultiplicity : (L : ℚ) * hypergeometricRatio ((n + (2 * k - 1)) / 2) n r *
      profile.tail (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator q g) a ≤
      (L : ℚ) * ((mid : ℚ) / m) * ((profile.labelsAtLeast a : ℚ) / ((q : ℚ) * s)) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (opening_nonneg _))
    exact (min_le_right _ _).trans_eq (by
      unfold SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
      push_cast
      rfl)
  calc
    _ ≤ (noLiftPeakNumerator n r d g outer : ℚ) / ((m : ℚ) * s) +
          (L : ℚ) * ((mid : ℚ) / m) * ((profile.labelsAtLeast a : ℚ) / ((q : ℚ) * s)) +
          (1 + (second : ℚ) / m + 2 * (L : ℚ) * ((other : ℚ) / m)) / q := by
      unfold highMassBound
      apply add_le_add _ le_rfl
      apply add_le_add _ hmultiplicity
      simpa only [Nat.cast_mul] using noLift_peak_bound (e := e) (r := r)
        (localBound := localBound) hq hd ha houter
    _ = (num : ℚ) / ((m : ℚ) * s * q) := by
      have heq : num = q * noLiftPeakNumerator n r d g outer + L * mid * profile.labelsAtLeast a +
          s * (m + second + 2 * L * other) := rfl
      rw [heq]
      push_cast
      field_simp
    _ ≤ (319 : ℚ) / (100 * q) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hz : (100 : ℚ) * num ≤ 319 * m * s := by exact_mod_cast hcheck
      calc
        _ = (q : ℚ) * (100 * num) := by ring
        _ ≤ (q : ℚ) * (319 * m * s) := mul_le_mul_of_nonneg_left hz hq'.le
        _ = _ := by ring

end LfzkV1.LigeroHighMass125
