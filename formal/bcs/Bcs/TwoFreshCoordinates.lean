import Bcs.TotalOracle

/-!
# Two fresh coordinates of a finite random oracle

When a proof is fixed before any transcript-hash query, its last two distinct
hash inputs are fixed coordinates of the total oracle.  Conditional on every
other answer, those two answers are independent uniform draws.  The lemma
below transports an exact accepting-pair count to the total-oracle sample
space.  It does not cover adaptive selection of either hash input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

abbrev AwayFromTwo (x y : Q) := { z : Q // z ≠ x ∧ z ≠ y }

/-- Separate two distinct oracle coordinates from all other answers. -/
def splitTwo (x y : Q) (hxy : x ≠ y) :
    (Q → C) ≃ ((AwayFromTwo x y → C) × (C × C)) where
  toFun H := (fun z => H z.1, (H x, H y))
  invFun p z :=
    if hz : z = x then p.2.1 else
    if hy : z = y then p.2.2 else p.1 ⟨z, hz, hy⟩
  left_inv H := by
    funext z
    by_cases hx : z = x
    · simp [hx]
    · by_cases hy : z = y
      · subst z
        simp [Ne.symm hxy]
      · simp [hx, hy]
  right_inv p := by
    rcases p with ⟨f, ⟨cx, cy⟩⟩
    apply Prod.ext
    · funext z
      simp [z.property.1, z.property.2]
    · apply Prod.ext
      · simp
      · simp [Ne.symm hxy]

/-- Exact rational sum after holding out two distinct oracle answers.  This
version supports the fractional query-cover weights used by the graded
Ligero response-mass certificate. -/
theorem sum_two_fresh_weight (x y : Q) (hxy : x ≠ y)
    (weight : (AwayFromTwo x y → C) → C → C → ℚ) :
    ∑ H : Q → C, weight (fun z => H z.1) (H x) (H y) =
      ∑ off : AwayFromTwo x y → C, ∑ a : C, ∑ b : C,
        weight off a b := by
  classical
  let e := splitTwo (C := C) x y hxy
  calc
    ∑ H : Q → C, weight (fun z => H z.1) (H x) (H y) =
        ∑ p : (AwayFromTwo x y → C) × (C × C),
          weight p.1 p.2.1 p.2.2 := by
            exact Fintype.sum_equiv e _ _ (by intro H; rfl)
    _ = ∑ off : AwayFromTwo x y → C, ∑ a : C, ∑ b : C,
          weight off a b := by
            simp only [Fintype.sum_prod_type]

end Bcs.TotalOracle
