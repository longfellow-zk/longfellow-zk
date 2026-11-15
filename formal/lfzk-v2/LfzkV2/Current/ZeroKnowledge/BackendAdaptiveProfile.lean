import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveJoint
import LfzkV2.Current.ZeroKnowledge.BackendProfile

/-! A fixed reference opening of the current backend: the first 84 of its
2443 columns, as an unordered query set. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Backend.Adaptive.Profile
open Polynomial Application LigeroFamily RecursivePolygero.Local
open scoped Classical

def referenceIndices : Fin 84 ↪ Fin 2443 where
  toFun i := ⟨i.val,by have := i.isLt; omega⟩
  inj' _ _ equal := Fin.ext (congrArg (fun i : Fin 2443 => i.val) equal)

def reference : QuerySet 2443 84 := OrderedOpening.query referenceIndices

end LfzkV2.Current.ZeroKnowledge.Backend.Adaptive.Profile
