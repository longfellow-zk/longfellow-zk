import LfzkV2.ChallengeTests
import LfzkV2.Events

/-! Challenge budgets computed from the trusted circuit dimensions. -/

namespace LfzkV2

open SumcheckV2
open scoped Classical

variable {F Pad Slot : Type} [Field F]

theorem assertionTests_budget_le (model : AssertedModel F) (claim : F) :
    (assertionTests model claim).budget ≤ min 1 model.assertions := by
  have hcard : (assertionIndices model).card ≤ model.assertions :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_fin _)
  simpa [assertionTests, Tests.budget, ChallengeTest.budget, Function.comp_def] using
    Nat.le_min.mpr ⟨assertionIndices_card_le_one model, hcard⟩

theorem layerTests_budget_le (model : LayerModel F) (t : LayerTranscript Pad Slot F)
    (pads : Pad → F) (claim : F) :
    (layerTests model t pads claim).budget ≤ 2 * model.logSize + 1 := by
  rw [layerTests, Tests.budget_append]
  change (roundTests _ _ _ _).budget + 1 ≤ _
  have h := roundTests_budget_le claim
    (truePolys (bindRight model.kernel model.wires) model.wires model.point)
    (t.clearRounds pads) t.challenges
  rw [truePolys_length] at h
  omega

namespace Circuit

def layerBudget : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) assertions _ rest =>
      assertions + 2 * mid + 1 + rest.layerBudget

theorem traceTests_budget_le {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) :
    (traceTests pads claim (circuit.execution messages w weights)).budget ≤ circuit.layerBudget := by
  induction circuit generalizing claim with
  | input => rfl
  | layer assertions body rest ih =>
      rcases messages with ⟨ml, mr⟩
      simp only [execution, traceTests, Tests.budget_append]
      have ha := (assertionTests_budget_le
        (body.model weights ml.beta (rest.eval w) ml.point) claim).trans (Nat.min_le_right _ _)
      have hl := layerTests_budget_le
        (body.model weights ml.beta (rest.eval w) ml.point).toLayerModel ml.transcript pads claim
      have hr := ih mr w
        (nextWeights (body.effective weights ml.beta) (monomialWeights ml.point) ml.alpha)
        (ml.transcript.clearA pads + ml.transcript.alpha * ml.transcript.clearB pads)
      change _ ≤ assertions + 2 * _ + 1 + rest.layerBudget
      change (layerTests _ _ _ _).budget ≤ 2 * _ + 1 at hl
      change _ ≤ rest.layerBudget at hr
      dsimp only [CircuitLayer.model] at ha hl ⊢
      change (assertionTests _ _).budget ≤ assertions at ha
      omega

/-- Assertion batching consumes one root test per layer, regardless of the
number of assertion occurrences in that layer. -/
def sharpLayerBudget : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) assertions _ rest =>
      min 1 assertions + 2 * mid + 1 + rest.sharpLayerBudget

theorem traceTests_budget_le_sharp {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) :
    (traceTests pads claim (circuit.execution messages w weights)).budget ≤ circuit.sharpLayerBudget := by
  induction circuit generalizing claim with
  | input => rfl
  | layer assertions body rest ih =>
      rcases messages with ⟨ml, mr⟩
      simp only [execution, traceTests, Tests.budget_append]
      have ha := assertionTests_budget_le (body.model weights ml.beta (rest.eval w) ml.point) claim
      have hl := layerTests_budget_le
        (body.model weights ml.beta (rest.eval w) ml.point).toLayerModel ml.transcript pads claim
      have hr := ih mr w
        (nextWeights (body.effective weights ml.beta) (monomialWeights ml.point) ml.alpha)
        (ml.transcript.clearA pads + ml.transcript.alpha * ml.transcript.clearB pads)
      change _ ≤ min 1 assertions + 2 * _ + 1 + rest.sharpLayerBudget
      change (layerTests _ _ _ _).budget ≤ 2 * _ + 1 at hl
      change _ ≤ rest.sharpLayerBudget at hr
      dsimp only [CircuitLayer.model] at ha hl ⊢
      change (assertionTests _ _).budget ≤ min 1 assertions at ha
      omega

/-- One per output fold and assertion, two per sumcheck round, one per combination.
Malformed message lists cannot increase this budget. -/
theorem tests_budget_le {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) :
    (circuit.tests messages w point pads).budget ≤ out + circuit.layerBudget := by
  rw [tests, Tests.budget_append, outputTests_budget]
  exact Nat.add_le_add_left (circuit.traceTests_budget_le messages w _ pads 0) out

theorem tests_budget_le_sharp {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) :
    (circuit.tests messages w point pads).budget ≤ out + circuit.sharpLayerBudget := by
  rw [tests, Tests.budget_append, outputTests_budget]
  exact Nat.add_le_add_left (circuit.traceTests_budget_le_sharp messages w _ pads 0) out

end Circuit

end LfzkV2
