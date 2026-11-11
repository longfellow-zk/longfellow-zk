import LfzkV2.Current.BackendOracle

/-! Opaque roles are the canonically decoded batching inputs and auxiliary
hash names. Opening's single test remains transparent. -/
noncomputable section
namespace Survival.RuntimeRoles
open LfzkV2.Current

variable {roles : List Role} {Key Block Link Body Aux : Type}

def marked (index : Fin roles.length) : Input roles Key Block Link Body ⊕ Aux → Bool
  | .inl point => (BackendOracle.parentOf (i := index) point).isSome
  | .inr _ => true

def auxiliary : Input roles Key Block Link Body ⊕ Aux → Bool
  | .inl _ => false
  | .inr _ => true

theorem marked_parent (index : Fin roles.length) (parent : BackendQueries.Parent roles Key Block Link index) :
    marked (Body := Body) (Aux := Aux) index (.inl parent.point) = true := by
  simp only [marked, BackendOracle.parentOf_point, Option.isSome_some]

end Survival.RuntimeRoles
