import LfzkV2.Inputs

/-! Honest masked messages and completeness of the symbolic compiler. -/

namespace LfzkV2

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

structure LayerPads (Pad Slot : Type) (n : ℕ) where
  round0 : Fin n → Pad
  round1 : Fin n → Pad
  claimA : Pad
  claimB : Pad
  productSlot : Slot

def maskedHonestRounds {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) : List (RoundPoly F × Pad × Pad) :=
  List.ofFn fun i : Fin n =>
    (mask ((honestMessages q w point).get (i.cast (honestMessages_length q w point).symm))
      ⟨pads (ids.round0 i), pads (ids.round1 i)⟩, ids.round0 i, ids.round1 i)

theorem unmask_honestRounds {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) :
    ((maskedHonestRounds q w point ids pads).map
      fun (m, p0, p1) => unmask m ⟨pads p0, pads p1⟩) = honestMessages q w point := by
  simp only [maskedHonestRounds, List.map_ofFn]
  apply List.ext_getElem
  · simp [honestMessages_length]
  · intro i hi hj
    simp

def honestLayer {n a : ℕ} (K : Cube n → Cube n → F) (w : Cube n → F)
    (point : Fin n → F) (alpha : F) (beta : Fin a → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) : LayerMessages Pad Slot F n a where
  messages := maskedHonestRounds (bindRight K w) w point ids pads
  point := point
  messageA := evaluate w point - pads ids.claimA
  messageB := evaluate (bindRight K w) point - pads ids.claimB
  padA := ids.claimA
  padB := ids.claimB
  productSlot := ids.productSlot
  alpha := alpha
  beta := beta

theorem honestLayer_honest {n a : ℕ} (K : Cube n → Cube n → F) (w : Cube n → F)
    (point : Fin n → F) (alpha : F) (beta : Fin a → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) :
    (LayerModel.mk n K w point).Honest (honestLayer K w point alpha beta ids pads).transcript pads := by
  refine ⟨unmask_honestRounds _ _ _ _ _, ?_, ?_⟩ <;>
    simp [honestLayer, LayerMessages.transcript, LayerTranscript.clearA, LayerTranscript.clearB]

namespace Circuit

/-- The pad names and sampled challenges used by an honest execution. This is
an algebraic transcript, not an implementation of the random oracle sampler. -/
structure LayerSetup (Pad Slot F : Type) (rounds assertions : ℕ) where
  pads : LayerPads Pad Slot rounds
  point : Fin rounds → F
  alpha : F
  beta : Fin assertions → F

def Setup (Pad Slot : Type) : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest =>
      LayerSetup Pad Slot F mid a × Setup Pad Slot rest

noncomputable def prove : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Setup Pad Slot → (Cube input → F) → (Cube out → F) →
    (Pad → F) → circuit.Messages Pad Slot
  | _, _, .input, _, _, _, _ => ()
  | _, _, .layer _ body rest, setup, w, weights, pads =>
      let K := body.effective weights setup.1.beta
      (honestLayer K (rest.eval w) setup.1.point setup.1.alpha setup.1.beta setup.1.pads pads,
        prove rest setup.2 w
          (nextWeights K (monomialWeights setup.1.point) setup.1.alpha) pads)

theorem prove_honest {out input : ℕ} (circuit : Circuit F out input)
    (setup : circuit.Setup Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) :
    ∀ entry ∈ circuit.execution (circuit.prove setup w weights pads) w weights,
      entry.2.toLayerModel.Honest entry.1 pads := by
  induction circuit with
  | input => simp [execution]
  | layer a body rest ih =>
      rcases setup with ⟨sl, sr⟩
      change ∀ entry ∈ (_, _) :: _, _
      rw [List.forall_mem_cons]
      exact ⟨honestLayer_honest _ _ _ _ _ _ _, ih sr _ _⟩

/-- If the witness is valid and every layer uses its masked honest messages,
the complete builder succeeds and returns satisfied symbolic equations. -/
theorem honest_constraints {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w)
    (hhonest : ∀ entry ∈ circuit.execution messages w (monomialWeights point),
      entry.2.toLayerModel.Honest entry.1 pads) :
    ∃ cs, buildConstraints (circuit.proof messages) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages (monomialWeights point)) w) := by
  apply (buildConstraints_correct _ _ _).mpr
  have hconsistent := circuit.execution_consistent messages w (monomialWeights point)
  have hno : ¬ HasViolation (circuit.execution messages w (monomialWeights point)) := by
    rw [execution_violation]
    exact not_not.mpr hvalid.2
  have ha := asserted_chain_completeness _ pads _ _ hconsistent hno hhonest
  have hz : dot (monomialWeights point) (circuit.eval w) = 0 := by
    rw [hvalid.1]
    simp [dot]
  simpa only [hz, execution_transcripts] using ha

/-- Construct the masked transcript and prove that the complete builder accepts
every satisfying circuit witness, for every choice of pads and challenges. -/
theorem prove_complete {out input : ℕ} (circuit : Circuit F out input)
    (setup : circuit.Setup Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w) :
    let messages := circuit.prove setup w (monomialWeights point) pads
    ∃ cs, buildConstraints (circuit.proof messages) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages (monomialWeights point)) w) :=
  circuit.honest_constraints _ w point pads hvalid
    (circuit.prove_honest setup w (monomialWeights point) pads)

end Circuit

end LfzkV2
