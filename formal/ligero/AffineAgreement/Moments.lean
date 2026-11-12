import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat

/-!
# Balanced agreement moments
-/

namespace AffineAgreement

namespace Internal

/-- Exact balanced third-binomial moment.  Internally this is the floor/ceiling
allocation of `total` incidences among `n` coordinates. -/
def balanced_choose_three (n total : ℕ) : ℕ :=
  let lo := total / n
  let hiCount := total % n
  (n - hiCount) * lo.choose 3 + hiCount * (lo + 1).choose 3

end Internal

export Internal (balanced_choose_three)

/-- Compatibility name for the canonical balanced third moment. -/
abbrev rounded_choose_three := balanced_choose_three

@[simp] theorem rounded_choose_three_eq_balanced_choose_three (n total : ℕ) :
    rounded_choose_three n total = balanced_choose_three n total := rfl

/-- Exact rational lower bound for the mean intersection of three equally
sized sets. -/
def tripleIntersectionMean (universeSize setSize familySize : ℕ) : ℚ :=
  (balanced_choose_three universeSize (familySize * setSize) : ℕ) /
    (familySize.choose 3 : ℚ)

end AffineAgreement
