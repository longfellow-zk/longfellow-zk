import LfzkV2.ChallengePrefix
import LfzkV2.Events
import SumcheckV1.Grinding

/-! Prefix-local replay of output folding and the selected assertion test. -/

namespace LfzkV2.AssertionReplay
open SumcheckV2 Finset
open scoped Classical
variable {F : Type} [Field F]

theorem assertionTests_eq (model : AssertedModel F) (claim : F) :
    assertionTests model claim = (assertionIndices model).toList.map (fun i =>
      (dataAt model.incoming claim model.residuals i (SumcheckV1.extract_prefix model.beta i),
        model.beta i)) := by
  unfold assertionTests
  apply List.map_congr_left
  intro i _
  rw [dataAt_eq]

/-- The selected assertion index is independent of output weights, assertion
challenges, and the later sumcheck point. -/
theorem indices_model_eq {Output : Type} [Fintype Output] {n a : ℕ}
    (layer : CircuitLayer Output (Cube n) (Fin a) F) (w : Cube n → F)
    (weights weights' : Output → F) (beta beta' : Fin a → F) (point point' : Fin n → F) :
    assertionIndices (layer.model weights beta w point) =
      assertionIndices (layer.model weights' beta' w point') := rfl

end LfzkV2.AssertionReplay
