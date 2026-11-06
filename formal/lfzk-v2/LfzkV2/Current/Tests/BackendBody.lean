import LfzkV2.Current.BackendBody
import Mathlib.Data.ZMod.Basic

namespace LfzkV2.Current.Tests.BackendBody
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩
private def nodes : Fin 2 → ZMod 101 := ![2, 3]
private def values : Fin 2 → ZMod 101 := ![5, 7]

private theorem distinct : Function.Injective nodes := by
  decide +kernel

-- Wire entries are evaluations at the oracle prefix, not coefficients.
-- A coefficient decoder for [5,7] would give 19 at node 2 and fail here.
example :
    (((Response.evaluationEquiv (ZMod 101) nodes distinct).symm values :
      Polynomial.degreeLT (ZMod 101) 2) : Polynomial (ZMod 101)).eval 2 = 5 :=
  Response.evaluationEquiv_eval (ZMod 101) nodes distinct values 0

example :
    (((Response.evaluationEquiv (ZMod 101) nodes distinct).symm values :
      Polynomial.degreeLT (ZMod 101) 2) : Polynomial (ZMod 101)).eval 3 = 7 :=
  Response.evaluationEquiv_eval (ZMod 101) nodes distinct values 1

end LfzkV2.Current.Tests.BackendBody
