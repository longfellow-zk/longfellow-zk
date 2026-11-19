import LfzkV2.Current.BackendChallenges
import Mathlib.Data.ZMod.Basic

noncomputable section
namespace LfzkV2.Current.Tests.BackendChallenges
open RecursivePolygero.Local.Polygero
open Current.BackendChallenges
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩
private def nodes : Fin 2 → ZMod 101 := ![2,3]
private theorem distinct : Function.Injective nodes := by decide +kernel
private def samples : Fin 3 → Fin 2 → ZMod 101 := ![![5,7],![11,17],![23,29]]
private def encoded := polynomialsEquiv 1 0 rfl nodes distinct samples

-- Different physical rows have different evaluation vectors. This checks
-- mask order, witness placement and evaluation decoding together.
example : (encoded (maskIndex .vCoefficient)).val.eval 2 = 5 := by
  have h := polynomialsEquiv_eval 1 0 rfl nodes distinct samples (maskIndex .vCoefficient) 0
  have hi : rowOrder 1 0 rfl (maskIndex .vCoefficient) = 0 := Fin.ext (rowOrder_u 1 0 rfl)
  simpa [hi,encoded,nodes,samples] using h

example : (encoded (maskIndex .zRCoefficient)).val.eval 3 = 17 := by
  have h := polynomialsEquiv_eval 1 0 rfl nodes distinct samples (maskIndex .zRCoefficient) 1
  have hi : rowOrder 1 0 rfl (maskIndex .zRCoefficient) = 1 := Fin.ext (rowOrder_m 1 0 rfl)
  simpa [hi,encoded,nodes,samples] using h

example : (encoded (coreIndex .linear (0 : Fin 1))).val.eval 2 = 23 := by
  have h := polynomialsEquiv_eval 1 0 rfl nodes distinct samples (coreIndex .linear (0 : Fin 1)) 0
  have hi : rowOrder 1 0 rfl (coreIndex .linear (0 : Fin 1)) = 2 := Fin.ext (rowOrder_witness 1 0 rfl 0)
  simpa [hi,encoded,nodes,samples] using h

-- Two affine scalars come before u's two samples, then m, then witness.
example : (unflatten (ZMod 101) 2 1 1 (fun i => (i.val : ZMod 101))).1 1 = 1 := rfl
example : (unflatten (ZMod 101) 2 1 1 (fun i => (i.val : ZMod 101))).2 0 0 = 2 := rfl
example : (unflatten (ZMod 101) 2 1 1 (fun i => (i.val : ZMod 101))).2 1 0 = 4 := rfl
example : (unflatten (ZMod 101) 2 1 1 (fun i => (i.val : ZMod 101))).2 2 1 = 7 := rfl

end LfzkV2.Current.Tests.BackendChallenges
