import LfzkV2.Current.OpeningBody

namespace LfzkV2.Current.Tests.OpeningBody
open LigeroFamily

-- The actual bounded wire representation supports the finite-oracle model.
-- An unconstrained List frontier would make this instance impossible.
example (g : Geometry) : Nonempty (Fintype (Current.OpeningBody.Authentication g)) :=
  ⟨inferInstance⟩

private def column : Fin 4 → ℕ := ![10, 20, 30, 40]

-- Runtime serializes u,m before the ordinary witness and fstar last.
-- A generic finite enumeration would not establish this physical order.
example : (Current.OpeningBody.leafEquiv ℕ 1 column).1.checkedMask .vCoefficient = 10 := rfl
example : (Current.OpeningBody.leafEquiv ℕ 1 column).1.checkedMask .zRCoefficient = 20 := rfl
example : (Current.OpeningBody.leafEquiv ℕ 1 column).1.core .linear (0 : Fin 1) = 30 := rfl
example : (Current.OpeningBody.leafEquiv ℕ 1 column).2 = 40 := rfl

example (values : Fin 4 → ℕ) :
    (Current.OpeningBody.leafEquiv ℕ 1).symm (Current.OpeningBody.leafEquiv ℕ 1 values) = values :=
  (Current.OpeningBody.leafEquiv ℕ 1).symm_apply_apply values

end LfzkV2.Current.Tests.OpeningBody
