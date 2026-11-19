import LfzkV2.Linear.Replay
import LfzkV2.Linear.Soundness
import SumcheckV2.LinearTerminalMasking

/-! Honest linear-terminal messages. The product-pad equality is used only
here, for completeness; it is absent from the verifier and soundness proofs. -/

namespace LfzkV2.Linear

open SumcheckV2

variable {F Pad : Type} [Field F]

noncomputable def honestLayer {out n a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin a) F)
    (weights : Cube out → F) (w : Cube n → F) (point : Fin n → F)
    (scale alpha : F) (beta : Fin a → F) (ids : Replay.LayerPads Pad n) (pads : Pad → F) :
    LayerMessages Pad F n a :=
  let q := bindRightAffine (body.effectiveQuadratic weights beta) (body.effectiveLinear weights beta) w
  let A := evaluate w point
  let B := evaluate q point
  { roundMessages i := mask
      ((honestMessages q w point).get (i.cast (honestMessages_length q w point).symm))
      ⟨pads (ids.round i).1, pads (ids.round i).2⟩
    roundPads := ids.round
    point := point
    beta := beta
    cross := A * pads ids.b + B * pads ids.a - pads ids.d
    scale := scale
    messageA := A + scale * pads ids.a
    messageB := B + scale * pads ids.b
    padA := ids.a
    padB := ids.b
    padAB := ids.ab
    padD := ids.d
    alpha := alpha }

theorem honestLayer_correct {out n a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin a) F)
    (weights : Cube out → F) (w : Cube n → F) (point : Fin n → F)
    (scale alpha : F) (beta : Fin a → F) (ids : Replay.LayerPads Pad n) (pads : Pad → F)
    (hproduct : pads ids.ab = pads ids.a * pads ids.b) :
    let Q := body.effectiveQuadratic weights beta
    let L := body.effectiveLinear weights beta
    let K := body.effectiveConstant weights
    let t := (honestLayer body weights w point scale alpha beta ids pads).transcript body weights
    (∃ terminal,
      verify_multi_round ((dot (bindRightAffine Q L w) w + K) - K)
        (t.clearRounds pads) t.challenges = some terminal ∧
      LinearTerminal.residual terminal t.cross t.scale t.messageA t.messageB (t.terminalPads pads) = 0) ∧
    t.nextValue pads = dot (nextWeights Q (monomialWeights point) alpha) w := by
  let Q := body.effectiveQuadratic weights beta
  let L := body.effectiveLinear weights beta
  let q := bindRightAffine Q L w
  let t := (honestLayer body weights w point scale alpha beta ids pads).transcript body weights
  have hr : t.clearRounds pads = honestMessages q w point := by
    simp only [t, honestLayer, LayerMessages.transcript, LayerTranscript.clearRounds, List.map_ofFn]
    apply List.ext_getElem
    · simp [honestMessages_length]
    · intro i hi hj
      simp [q, Q, L]
  have hA : t.clearA pads = evaluate w point := by
    simp [t, honestLayer, LayerMessages.transcript, LayerTranscript.clearA,
      LayerTranscript.terminalPads, LinearTerminal.clearA]
  have hB : t.clearB pads = evaluate q point := by
    simp [t, honestLayer, LayerMessages.transcript, LayerTranscript.clearB,
      LayerTranscript.terminalPads, LinearTerminal.clearB, q, Q, L]
  have h := affine_layer_completeness Q L w (body.effectiveConstant weights) point alpha
  constructor
  · refine ⟨evaluate w point * evaluate q point, ?_, ?_⟩
    · change verify_multi_round _ (t.clearRounds pads) _ = _
      rw [hr]
      exact h.1
    · change LinearTerminal.residual _ t.cross t.scale t.messageA t.messageB (t.terminalPads pads) = 0
      simp only [t, honestLayer, LayerMessages.transcript, LayerTranscript.terminalPads, hproduct]
      exact LinearTerminal.completeness _ _ _ _ _ _
  · change t.nextValue pads = _
    unfold LayerTranscript.nextValue
    rw [hA, hB]
    exact h.2

namespace Circuit

structure LayerSetup (Pad F : Type) [Field F] (rounds assertions : ℕ) where
  pads : Replay.LayerPads Pad rounds
  point : Fin rounds → F
  scale : TerminalSampling.Nonzero F
  alpha : F
  beta : Fin assertions → F

abbrev Setup (Pad : Type) : {out input : ℕ} → Native.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest => LayerSetup Pad F mid a × Setup Pad rest

def HonestPads : {out input : ℕ} → (circuit : Native.Circuit F out input) →
    Setup Pad circuit → (Pad → F) → Prop
  | _, _, .input, _, _ => True
  | _, _, .layer _ _ rest, setup, pads =>
      pads setup.1.pads.ab = pads setup.1.pads.a * pads setup.1.pads.b ∧
        HonestPads rest setup.2 pads

noncomputable def prove : {out input : ℕ} → (circuit : Native.Circuit F out input) →
    Setup Pad circuit → (Cube input → F) → (Cube out → F) → (Pad → F) → Messages Pad circuit
  | _, _, .input, _, _, _, _ => ()
  | _, _, .layer _ body rest, setup, w, weights, pads =>
      let Q := body.effectiveQuadratic weights setup.1.beta
      (honestLayer body weights (rest.eval w) setup.1.point setup.1.scale.val setup.1.alpha
        setup.1.beta setup.1.pads pads,
        prove rest setup.2 w (nextWeights Q (monomialWeights setup.1.point) setup.1.alpha) pads)

theorem prove_clear {out input : ℕ} (circuit : Native.Circuit F out input)
    (setup : Setup Pad circuit) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (hvalid : circuit.AssertionsValid w) (hpads : HonestPads circuit setup pads) :
    let m := prove circuit setup w weights pads
    ClearAccepts pads (dot weights (circuit.eval w)) (proof circuit m weights)
      (dot (inputWeights circuit m weights) w) := by
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
      let m := honestLayer body weights wires sl.point sl.scale.val sl.alpha sl.beta sl.pads pads
      have hlayer := honestLayer_correct body weights wires sl.point sl.scale.val sl.alpha sl.beta
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
      · change ClearAccepts pads ((m.transcript body weights).nextValue pads)
          (proof rest (prove rest sr w next pads) next)
          (dot (inputWeights rest (prove rest sr w next pads) next) w)
        rw [hlayer.2]
        exact ih sr w next hrest hpads.2

theorem prove_complete {out input : ℕ} (circuit : Native.Circuit F out input)
    (setup : Setup Pad circuit) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hvalid : circuit.Satisfies w) (hpads : HonestPads circuit setup pads) :
    let m := prove circuit setup w (monomialWeights point) pads
    ∃ cs, buildConstraints (proof circuit m (monomialWeights point)) = some cs ∧
      cs.Holds pads (dot (inputWeights circuit m (monomialWeights point)) w) := by
  apply (buildConstraints_correct _ _ _).mpr
  have h := prove_clear circuit setup w (monomialWeights point) pads hvalid.2 hpads
  simpa [hvalid.1, dot] using h

end Circuit
end LfzkV2.Linear
