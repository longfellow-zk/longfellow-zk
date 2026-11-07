import LfzkV2.Current.ZeroKnowledge.BackendProfile
import LfzkV2.Current.ZeroKnowledge.BackendInterpolation

/-! Backend simulator regression and axiom audits.  In particular the
simulator must work without receiving any satisfying witness. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackend
open LigeroFamily RecursivePolygero.Local
open ZeroKnowledge.Backend

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def impossible : ConstraintSystem F 0 0 265 (Fin 1) where
  coefficient := fun _ _ _ _ => 0
  target := fun _ => 1

omit [Fintype F] [DecidableEq F] in
theorem impossible_unsatisfied : ¬∃ cells : Cells F 0 265, impossible.Satisfies (logical cells) := by
  rintro ⟨cells,h⟩
  have heq := h.1 0
  simp [ConstraintSystem.linearValue,impossible] at heq

/-- Knowing the sampled opening set permits the public simulator to hide
an impossible statement's residual away from those openings. Fiat--Shamir
simulation must therefore program that one set; this is not a prover attack. -/
example (nodes : Fin 2792 ↪ F) (Q : QuerySet 2443 84)
    (coin : Polygero.Coin F (Fin 1) 0 0 12)
    (tape : Tape (profileGeometry nodes) 0 12) :
    Polygero.verify (profileGeometry nodes).domain (profileGeometry nodes).k_le_n
      (ConstraintLayout.identity 265) impossible coin
      (simulate (profileGeometry nodes) Q 0 impossible coin tape).2 Q
      (simulate (profileGeometry nodes) Q 0 impossible coin tape).1 = true :=
  simulate_verifies (profileGeometry nodes) (by decide) Q 0 impossible coin tape

#print axioms compatible
#print axioms simulate_verifies
#print axioms coupling_view
#print axioms jointSimulate_verifies
#print axioms joint_sameDistribution
#print axioms profileSimulate_verifies
#print axioms profile_wire_sameDistribution
#print axioms jointProfile_wire_sameDistribution
#print axioms correctionBase_eq_polynomial
#print axioms simulate_primary_sample
#print axioms real_primary_sample
end LfzkV2.Current.Tests.ZeroKnowledgeBackend
