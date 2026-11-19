import LfzkV2.Layered.Fragments

/-! Sparse fragments supply the ordinary tensor layer used by soundness.
Duplicate terms and overlapping input ranges contribute additively. The
assertion stream remains independently indexed, as in the ordinary layer. -/

namespace LfzkV2.Layered

open SumcheckV2
open scoped Classical

variable {F O W A : Type} [Field F] [Fintype W]

namespace Term

noncomputable def quadraticKernel (g : O) (l r : W) : Term O W F → F
  | .quadratic g' l' r' k => if g' = g ∧ l' = l ∧ r' = r then k else 0
  | _ => 0

noncomputable def linearKernel (g : O) (l : W) : Term O W F → F
  | .linear g' l' k => if g' = g ∧ l' = l then k else 0
  | _ => 0

noncomputable def constantKernel (g : O) : Term O W F → F
  | .constant g' k => if g' = g then k else 0
  | _ => 0

theorem kernels_value (term : Term O W F) (w : W → F) (g : O) :
    LfzkV2.quadratic (fun l r => term.quadraticKernel g l r) w +
      dot (fun l => term.linearKernel g l) w + term.constantKernel g =
      term.evaluated w g := by
  cases term <;>
    simp [LfzkV2.quadratic, dot, quadraticKernel, linearKernel, constantKernel,
      evaluated, output, value, ite_and]

end Term

noncomputable def sparseLayer (terms : List (Term O W F))
    (assertions : A → Native.AssertionTerm W) : Native.CircuitLayer O W A F where
  quadratic g l r := (terms.map (Term.quadraticKernel g l r)).sum
  linear g l := (terms.map (Term.linearKernel g l)).sum
  constant g := (terms.map (Term.constantKernel g)).sum
  assertions := assertions

theorem sparseLayer_outputs (terms : List (Term O W F))
    (assertions : A → Native.AssertionTerm W) (w : W → F) (g : O) :
    (sparseLayer terms assertions).outputs w g = (terms.map (Term.evaluated w g)).sum := by
  induction terms with
  | nil => simp [sparseLayer, Native.CircuitLayer.outputs, LfzkV2.quadratic, dot]
  | cons term terms ih =>
      have hterm := term.kernels_value w g
      simp only [Native.CircuitLayer.outputs, sparseLayer, List.map_cons, List.sum_cons,
        LfzkV2.quadratic_add, Native.dot_add_left] at ih ⊢
      linear_combination hterm + ih

end LfzkV2.Layered
