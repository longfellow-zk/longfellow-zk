import CodingTheory.ListDecoding.HahnDelsarte

/-! Independent checks of consecutive radius ranges for a Hahn certificate. -/

namespace CodingTheory.HahnDelsarte

/-- The polynomial-sign check on radii in `[lo, hi)`. -/
def certificateRangeValid (n w lo hi : ℕ) (coeffs : List ℕ) : Bool :=
  (List.range (hi - lo)).all fun offset ↦
    let t := lo + offset
    decide (n + t < 2 * w) || decide (certificatePolynomial n w coeffs t ≤ 0)

/-- Checked ranges cover the original certificate when they cover every
admissible radius.  The final assembly uses the range proofs as opaque facts;
it does not evaluate the polynomial again. -/
theorem certificateValid_of_ranges (n w lam : ℕ) (coeffs : List ℕ)
    (ranges : List (ℕ × ℕ))
    (hpos : 0 < coeffs.headD 0)
    (hcover : ∀ t ≤ lam, ∃ p ∈ ranges, p.1 ≤ t ∧ t < p.2)
    (hchecks : ∀ p ∈ ranges,
      certificateRangeValid n w p.1 p.2 coeffs = true) :
    certificateValid n w lam coeffs = true := by
  unfold certificateValid
  simp only [Bool.and_eq_true]
  constructor
  · exact decide_eq_true hpos
  · apply List.all_eq_true.mpr
    intro t ht
    obtain ⟨⟨lo, hi⟩, hp, hlo, hhi⟩ := hcover t
      (Nat.lt_succ_iff.mp (List.mem_range.mp ht))
    have hr := hchecks (lo, hi) hp
    simp only [certificateRangeValid, List.all_eq_true] at hr
    have hoff : t - lo ∈ List.range (hi - lo) :=
      List.mem_range.mpr (by omega)
    simpa only [Nat.add_sub_of_le hlo] using hr (t - lo) hoff

end CodingTheory.HahnDelsarte
