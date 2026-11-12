import LfzkV2.LayerMessages
import LfzkV2.AssertedSoundness

/-!
# Trusted layered circuits and verifier reconstruction

Circuits are indexed by their padded input/output table dimensions. Evaluation
runs from inputs toward outputs. Reconstruction runs in the reverse direction,
using only the public tensors, proof messages, and sampled challenges to compute
the final input weights. No assertion-validity premise is used by reconstruction.
-/

namespace LfzkV2

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

inductive Circuit (F : Type) : ℕ → ℕ → Type where
  | input {n : ℕ} : Circuit F n n
  | layer {out mid input : ℕ} (assertions : ℕ)
      (body : CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
      (rest : Circuit F mid input) : Circuit F out input

namespace Circuit

abbrev Messages (Pad Slot : Type) : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest =>
      LayerMessages Pad Slot F mid a × Messages Pad Slot rest

noncomputable def eval : {out input : ℕ} → Circuit F out input → (Cube input → F) → Cube out → F
  | _, _, .input, w => w
  | _, _, .layer _ body rest, w => body.outputs (eval rest w)

def AssertionsValid : {out input : ℕ} → Circuit F out input → (Cube input → F) → Prop
  | _, _, .input, _ => True
  | _, _, .layer _ body rest, w =>
      (∀ i, body.residuals (eval rest w) i = 0) ∧ AssertionsValid rest w

def Satisfies {out input : ℕ} (circuit : Circuit F out input) (w : Cube input → F) : Prop :=
  circuit.eval w = 0 ∧ circuit.AssertionsValid w

def proof : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → List (LayerTranscript Pad Slot F)
  | _, _, .input, _ => []
  | _, _, .layer _ _ rest, m => m.1.transcript :: proof rest m.2

noncomputable def inputWeights : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube out → F) → Cube input → F
  | _, _, .input, _, weights => weights
  | _, _, .layer _ body rest, m, weights =>
      inputWeights rest m.2
        (nextWeights (body.effective weights m.1.beta) (monomialWeights m.1.point) m.1.alpha)

noncomputable def execution : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube input → F) → (Cube out → F) → AssertedTrace Pad Slot F
  | _, _, .input, _, _, _ => []
  | _, _, .layer _ body rest, m, w, weights =>
      (m.1.transcript, body.model weights m.1.beta (eval rest w) m.1.point) ::
        execution rest m.2 w
          (nextWeights (body.effective weights m.1.beta) (monomialWeights m.1.point) m.1.alpha)

/-- The reconstructed proof messages are independent of the witness. -/
theorem execution_transcripts {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F) :
    assertedTranscripts (circuit.execution m w weights) = circuit.proof m := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      change m.1.transcript :: assertedTranscripts (rest.execution m.2 w
        (nextWeights (body.effective weights m.1.beta) (monomialWeights m.1.point) m.1.alpha)) =
        m.1.transcript :: rest.proof m.2
      rw [ih]

/-- The layer-chain invariant follows from reconstruction, including for invalid assertions. -/
theorem execution_consistent {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F) :
    TraceConsistent (dot weights (circuit.eval w)) (circuit.execution m w weights)
      (dot (circuit.inputWeights m weights) w) := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      refine ⟨rfl, rfl, ?_⟩
      exact ih m.2 w _

theorem execution_violation {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F) :
    HasViolation (circuit.execution m w weights) ↔ ¬ circuit.AssertionsValid w := by
  induction circuit with
  | input => simp [execution, HasViolation, AssertionsValid]
  | layer a body rest ih =>
      rcases m with ⟨ml, mr⟩
      change HasViolation ((ml.transcript, body.model weights ml.beta (rest.eval w)
        ml.point) :: _) ↔ _
      rw [hasViolation_cons, ih mr w]
      change ((∃ i, body.residuals (rest.eval w) i ≠ 0) ∨ ¬ rest.AssertionsValid w) ↔
        ¬ ((∀ i, body.residuals (rest.eval w) i = 0) ∧ rest.AssertionsValid w)
      simp only [not_and_or, not_forall]

/-- False circuit witnesses accepted by the clear verifier yield one of the
bounded challenge events. Circuit evaluation and layer consistency are proved. -/
theorem soundness_reduction {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof m)
      (dot (circuit.inputWeights m (monomialWeights point)) w)) :
    OutputBad (circuit.eval w) point ∨
      AssertedBad pads 0 (circuit.execution m w (monomialWeights point)) := by
  apply circuit_reduction (circuit.eval w) point _ pads _
  · rw [evaluate_eq_dot]
    exact circuit.execution_consistent m w (monomialWeights point)
  · simpa only [execution_transcripts] using haccept
  · rw [execution_violation]
    simpa only [Satisfies, not_and_or] using hfalse

end Circuit

end LfzkV2
