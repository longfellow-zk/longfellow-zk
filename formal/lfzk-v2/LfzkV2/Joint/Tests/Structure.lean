import LfzkV2.Joint.Causality
import LfzkV2.Joint.Pair
import LfzkV2.Joint.Potential
import LfzkV2.Joint.RuntimeCost

/-! Small structural checks for tuple positions and the shared-query bound. -/

namespace LfzkV2.Joint.Tests

open Finset

variable {k s n t : ℕ}

def singleton (P : Participant k s n t) : Family k s n t :=
  ⟨1,by decide,fun _ => P⟩

example (P : Participant k s n t) : (singleton P).count = 1 := rfl

example (P : Participant k s n t) (first second : P.Oracle) :
    Pair.oracleEquiv P P ((Pair.oracleEquiv P P).symm (first,second)) = (first,second) :=
  (Pair.oracleEquiv P P).apply_symm_apply _

example (P : Participant k s n t) (first second : P.Oracle) (hne : first ≠ second) :
    ((Pair.oracleEquiv P P).symm (first,second)) (0 : Fin 2) ≠
      ((Pair.oracleEquiv P P).symm (first,second)) (1 : Fin 2) := hne

/-- Perfectly correlated field events show why a product of error rates is
invalid when the verifier reuses one query. -/
example : ((univ.filter fun b : Bool => b = true ∧ b = true).card : ℚ)/2 = 1/2 ∧
    (1/2 : ℚ) > (1/2 : ℚ)*(1/2 : ℚ) := by
  have h : (univ.filter fun b : Bool => b = true ∧ b = true) = {true} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, and_self, mem_singleton]
  rw [h]
  norm_num

example : RuntimeCost.coefficient = 1384/(2^128 : ℚ) := rfl
example : 1384 = 925+459 := rfl

end LfzkV2.Joint.Tests
