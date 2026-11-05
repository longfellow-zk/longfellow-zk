import LfzkV2.Native.Soundness
import LfzkV2.Prover

/-! Honest native affine messages, using the shared masking construction. -/

namespace LfzkV2.Native

open SumcheckV2

variable {F Pad Slot : Type} [Field F]

def honestLayer {n a : ℕ} (Q : Cube n → Cube n → F) (L w : Cube n → F)
    (point : Fin n → F) (alpha : F) (beta : Fin a → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) : LfzkV2.LayerMessages Pad Slot F n a where
  messages := maskedHonestRounds (bindRightAffine Q L w) w point ids pads
  point := point
  messageA := evaluate w point - pads ids.claimA
  messageB := evaluate (bindRightAffine Q L w) point - pads ids.claimB
  padA := ids.claimA
  padB := ids.claimB
  productSlot := ids.productSlot
  alpha := alpha
  beta := beta

theorem honestLayer_correct {n a : ℕ} (Q : Cube n → Cube n → F) (L w : Cube n → F)
    (K : F) (point : Fin n → F) (alpha : F) (beta : Fin a → F)
    (ids : LayerPads Pad Slot n) (pads : Pad → F) :
    let m := honestLayer Q L w point alpha beta ids pads
    let t : LayerTranscript Pad Slot F := ⟨m.transcript, K, evaluate L point⟩
    verify_multi_round ((dot (bindRightAffine Q L w) w + K) - K)
        (m.transcript.clearRounds pads) m.transcript.challenges =
      some (m.transcript.clearA pads * m.transcript.clearB pads) ∧
      t.nextValue pads = dot (nextWeights Q (monomialWeights point) alpha) w := by
  let m := honestLayer Q L w point alpha beta ids pads
  have hr : m.transcript.clearRounds pads =
      honestMessages (bindRightAffine Q L w) w point := unmask_honestRounds ..
  have hA : m.transcript.clearA pads = evaluate w point := by
    simp [m, honestLayer, LfzkV2.LayerMessages.transcript, LfzkV2.LayerTranscript.clearA]
  have hB : m.transcript.clearB pads = evaluate (bindRightAffine Q L w) point := by
    simp [m, honestLayer, LfzkV2.LayerMessages.transcript, LfzkV2.LayerTranscript.clearB]
  have h := affine_layer_completeness Q L w K point alpha
  change verify_multi_round _ (m.transcript.clearRounds pads) _ = _ ∧ _
  constructor
  · rw [hr, hA, hB]
    exact h.1
  · change m.transcript.clearA pads + alpha * (m.transcript.clearB pads - _) = _
    rw [hA, hB]
    exact h.2

namespace Circuit

def Setup (Pad Slot : Type) : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest =>
      LfzkV2.Circuit.LayerSetup Pad Slot F mid a × Setup Pad Slot rest

noncomputable def prove : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Setup Pad Slot → (Cube input → F) → (Cube out → F) →
    (Pad → F) → circuit.Messages Pad Slot
  | _, _, .input, _, _, _, _ => ()
  | _, _, .layer _ body rest, setup, w, weights, pads =>
      let Q := body.effectiveQuadratic weights setup.1.beta
      let L := body.effectiveLinear weights setup.1.beta
      (honestLayer Q L (rest.eval w) setup.1.point setup.1.alpha setup.1.beta setup.1.pads pads,
        prove rest setup.2 w
          (nextWeights Q (monomialWeights setup.1.point) setup.1.alpha) pads)

theorem prove_clear {out input : ℕ} (circuit : Circuit F out input)
    (setup : circuit.Setup Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (hvalid : circuit.AssertionsValid w) :
    let m := circuit.prove setup w weights pads
    ClearAccepts pads (dot weights (circuit.eval w)) (circuit.proof m weights)
      (dot (circuit.inputWeights m weights) w) := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      rcases setup with ⟨sl, sr⟩
      rcases hvalid with ⟨hvalid, hrest⟩
      let Q := body.effectiveQuadratic weights sl.beta
      let L := body.effectiveLinear weights sl.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      let next := nextWeights Q (monomialWeights sl.point) sl.alpha
      let m := honestLayer Q L wires sl.point sl.alpha sl.beta sl.pads pads
      have hlayer := honestLayer_correct Q L wires K sl.point sl.alpha sl.beta sl.pads pads
      have htruth : dot (bindRightAffine Q L wires) wires + K =
          dot weights (body.outputs wires) := by
        have h := body.effective_truth weights sl.beta wires
        have hzero : ∀ i, body.residuals wires i = 0 := hvalid
        simpa [dot, hzero] using h
      constructor
      · change verify_multi_round (dot weights (body.outputs wires) - K)
          (m.transcript.clearRounds pads) m.transcript.challenges = _
        rw [← htruth]
        exact hlayer.1
      · change ClearAccepts pads
          ((⟨m.transcript, K, evaluate L sl.point⟩ : LayerTranscript Pad Slot F).nextValue pads)
          (rest.proof (rest.prove sr w next pads) next)
          (dot (rest.inputWeights (rest.prove sr w next pads) next) w)
        rw [hlayer.2]
        exact ih sr w next hrest

/-- Honest construction satisfies the current corrected builder for every choice
of pads and challenges, including scalar layers and empty circuit chains. -/
theorem prove_complete {out input : ℕ} (circuit : Circuit F out input)
    (setup : circuit.Setup Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w) :
    let m := circuit.prove setup w (monomialWeights point) pads
    ∃ cs, Native.buildConstraints (circuit.proof m (monomialWeights point)) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights m (monomialWeights point)) w) := by
  apply (Native.buildConstraints_correct _ _ _).mpr
  have h := circuit.prove_clear setup w (monomialWeights point) pads hvalid.2
  simpa [hvalid.1, dot] using h

end Circuit

end LfzkV2.Native
