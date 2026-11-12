import LfzkV2.Layered.Soundness
import LfzkV2.Linear.Prover

/-! Honest layered sumcheck shares the existing numerical layer prover.
Entries update only weights and preserve the running claim when their outputs
vanish. Product-pad consistency appears only in honest completeness. -/

namespace LfzkV2.Layered

open SumcheckV2

variable {F Pad : Type} [Field F]

namespace Circuit

abbrev LayerSetup := Linear.Circuit.LayerSetup

abbrev Setup (Pad : Type) : {out input : ℕ} → Layered.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .entry n _ rest => (Fin n → F) × Setup Pad rest
  | _, _, .layer (mid := mid) a _ rest => LayerSetup Pad F mid a × Setup Pad rest

def HonestPads : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Setup Pad circuit → (Pad → F) → Prop
  | _, _, .input, _, _ => True
  | _, _, .entry _ _ rest, setup, pads => HonestPads rest setup.2 pads
  | _, _, .layer _ _ rest, setup, pads =>
      pads setup.1.pads.ab = pads setup.1.pads.a * pads setup.1.pads.b ∧
        HonestPads rest setup.2 pads

noncomputable def prove : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Setup Pad circuit → (Cube input → F) → (Cube out → F) → (Pad → F) → Messages Pad circuit
  | _, _, .input, _, _, _, _ => ()
  | _, _, .entry _ e rest, setup, w, weights, pads =>
      (setup.1, prove rest setup.2 w (e.weights weights setup.1) pads)
  | _, _, .layer _ body rest, setup, w, weights, pads =>
      let Q := body.effectiveQuadratic weights setup.1.beta
      (Linear.honestLayer body weights (rest.eval w) setup.1.point setup.1.scale.val setup.1.alpha
        setup.1.beta setup.1.pads pads,
        prove rest setup.2 w (nextWeights Q (monomialWeights setup.1.point) setup.1.alpha) pads)

theorem prove_clear {out input : ℕ} (circuit : Layered.Circuit F out input)
    (setup : Setup Pad circuit) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w) (hpads : HonestPads circuit setup pads) :
    let m := prove circuit setup w weights pads
    Linear.ClearAccepts pads (dot weights (circuit.eval w)) (proof circuit m weights)
      (dot (inputWeights circuit m weights) w) := by
  induction circuit with
  | input => rfl
  | entry n e rest ih =>
      have h := ih setup.2 w (e.weights weights setup.1) hvalid.2 hpads
      change Linear.ClearAccepts _ (dot (e.weights weights setup.1) (rest.eval w)) _ _ at h
      rw [e.dot_weights_of_zero weights setup.1 (rest.eval w) hvalid.1] at h
      exact h
  | layer a body rest ih =>
      rcases setup with ⟨sl, sr⟩
      rcases hvalid with ⟨hvalid, hrest⟩
      let Q := body.effectiveQuadratic weights sl.beta
      let L := body.effectiveLinear weights sl.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      let next := nextWeights Q (monomialWeights sl.point) sl.alpha
      let m := Linear.honestLayer body weights wires sl.point sl.scale.val sl.alpha sl.beta sl.pads pads
      have hlayer := Linear.honestLayer_correct body weights wires sl.point sl.scale.val sl.alpha sl.beta
        sl.pads pads hpads.1
      have htruth : dot (bindRightAffine Q L wires) wires + K = dot weights (body.outputs wires) := by
        have h := body.effective_truth weights sl.beta wires
        have hzero : ∀ i, body.residuals wires i = 0 := hvalid
        simpa [dot, hzero] using h
      constructor
      · change ∃ terminal, verify_multi_round (dot weights (body.outputs wires) - K)
          ((m.transcript body weights).clearRounds pads) _ = some terminal ∧ _
        rw [← htruth]
        exact hlayer.1
      · change Linear.ClearAccepts pads ((m.transcript body weights).nextValue pads)
          (proof rest (prove rest sr w next pads) next)
          (dot (inputWeights rest (prove rest sr w next pads) next) w)
        rw [hlayer.2]
        exact ih sr w next hrest hpads.2

theorem prove_complete {out input : ℕ} (circuit : Layered.Circuit F out input)
    (setup : Setup Pad circuit) (w : Cube input → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w) (hpads : HonestPads circuit setup pads) :
    let m := prove circuit setup w 0 pads
    ∃ cs, Linear.buildConstraints (proof circuit m 0) = some cs ∧
      cs.Holds pads (dot (inputWeights circuit m 0) w) := by
  apply (Linear.buildConstraints_correct _ _ _).mpr
  have h := prove_clear circuit setup w 0 pads hvalid hpads
  simpa [dot] using h

end Circuit
end LfzkV2.Layered
