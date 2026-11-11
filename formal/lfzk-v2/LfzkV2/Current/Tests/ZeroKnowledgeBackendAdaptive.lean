import LfzkV2.Current.ZeroKnowledge.BackendAdaptiveProfile

/-! Public response-fiber API and axiom checks. Ordered, response-dependent
selection and its failure case remain inside the exact joint-view theorem. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendAdaptive
open LigeroFamily RecursivePolygero.Local
open ZeroKnowledge.Backend ZeroKnowledge.Backend.Adaptive
open scoped Classical

#check @Adaptive.normalize
#check @normalizeFiber
#check @Adaptive.simulate
#check @Profile.simulate
#print axioms baseDelta_witness
#print axioms maskDelta_response
#print axioms normalize_payload
#print axioms normalizeFiber
#print axioms baseDelta_eq_polynomial
#print axioms selectionEquiv
#print axioms adaptiveCoupling_view
#print axioms Adaptive.sameDistribution
#print axioms Profile.sameDistribution

variable {B N : Type} [Field B] [Field N] [Fintype B] [Fintype N]
variable {r w n bw nw s : ℕ}
variable (binary : PolygeroZk.Geometry B r w 0 n) (prime : PolygeroZk.Geometry N r w 0 n)
variable {BE NE : Type} [Fintype BE] [Fintype NE]
variable (reference : QuerySet n r) (pivot : Fin w)
variable (statements : ConstraintSystem B bw 0 w BE × ConstraintSystem N nw 0 w NE)
variable (coins : Polygero.Coin B BE bw 0 s × Polygero.Coin N NE nw 0 s)

/-- A rejected actual reader does not acquire invented columns. This API
test requires no witness, even for the failure branch. -/
example (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    (Adaptive.simulate binary prime reference pivot statements coins id (fun _ => none) tape).2 = none := rfl

/-- Selection may inspect either field's complete response and retain
extra public state. Neither the selector nor that state is resampled. -/
example {Selection : Type} (queryOf : Selection → QuerySet n r)
    (select : Responses (B := B) (N := N) (r := r) (w := w) (s := s) → Option Selection)
    (tape : JointTape (bw := bw) (nw := nw) (s := s) binary prime) :
    ((Adaptive.simulate binary prime reference pivot statements coins queryOf select tape).2.map Sigma.fst) =
      select (publicResponse binary prime pivot statements coins reference tape) := by
  unfold Adaptive.simulate
  dsimp only
  cases select (publicResponse binary prime pivot statements coins reference tape) <;> rfl

end LfzkV2.Current.Tests.ZeroKnowledgeBackendAdaptive
