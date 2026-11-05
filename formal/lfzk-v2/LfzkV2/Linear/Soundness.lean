import LfzkV2.Linear.Circuit
import LfzkV2.Inputs

/-!
# Native circuit soundness with randomized affine terminals

The reduction includes every layer, assertion, affine correction, and the
initial output check. A false accepted circuit encounters a round, terminal,
combination, assertion, or output bad event. Candidate products are arbitrary
throughout this argument.
-/

namespace LfzkV2.Linear

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

def LayerTranscript.finalClaim (t : LayerTranscript Pad F) (pads : Pad → F) (claim : F) : F :=
  (verify_multi_round (claim - t.constant) (t.clearRounds pads) t.challenges).getD 0

namespace Circuit

noncomputable def Bad : {out input : ℕ} → (circuit : Native.Circuit F out input) →
    Messages Pad circuit → (Cube input → F) → (Cube out → F) → (Pad → F) → F → Prop
  | _, _, .input, _, _, _, _, _ => False
  | _, _, .layer _ body rest, m, w, weights, pads, claim =>
      let Q := body.effectiveQuadratic weights m.1.beta
      let L := body.effectiveLinear weights m.1.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      let q := bindRightAffine Q L wires
      let t := m.1.transcript body weights
      AssertionBad (dot weights (body.outputs wires)) claim m.1.beta (body.residuals wires) ∨
        (multi_round_bad_event (claim - K) (truePolys q wires m.1.point)
            (t.clearRounds pads) (List.ofFn m.1.point) ∨
          (LinearTerminal.Data.mk (t.finalClaim pads claim) (evaluate wires m.1.point)
            (evaluate q m.1.point) t.cross (t.terminalPads pads)).Bad t.scale ∨
          BadCombineEvent (evaluate wires m.1.point) (evaluate q m.1.point)
            (t.clearA pads) (t.clearB pads) t.alpha) ∨
        Bad rest m.2 w (nextWeights Q (monomialWeights m.1.point) m.1.alpha) pads
          (t.nextValue pads)

theorem reduction {out input : ℕ} (circuit : Native.Circuit F out input)
    (m : Messages Pad circuit) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (haccept : ClearAccepts pads claim (proof circuit m weights)
      (dot (inputWeights circuit m weights) w))
    (hdoom : claim ≠ dot weights (circuit.eval w) ∨ ¬ circuit.AssertionsValid w) :
    Bad circuit m w weights pads claim := by
  induction circuit generalizing claim with
  | input =>
      rcases hdoom with hfalse | hfalse
      · exact (hfalse haccept).elim
      · exact (hfalse trivial).elim
  | layer a body rest ih =>
      rcases m with ⟨ml, mr⟩
      let Q := body.effectiveQuadratic weights ml.beta
      let L := body.effectiveLinear weights ml.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      let q := bindRightAffine Q L wires
      let next := nextWeights Q (monomialWeights ml.point) ml.alpha
      let t := ml.transcript body weights
      rcases haccept with ⟨⟨terminal, hrounds, hrow⟩, htail⟩
      have hterminal : t.finalClaim pads claim = terminal := by
        change (verify_multi_round _ _ _).getD 0 = _
        rw [hrounds]
        rfl
      have htruth : dot q wires + K =
          dot weights (body.outputs wires) + dot ml.beta (body.residuals wires) :=
        body.effective_truth weights ml.beta wires
      by_cases hclaim : claim = dot q wires + K
      · by_cases hbad : ∃ i, body.residuals wires i ≠ 0
        · exact Or.inl (assertion_reduction _ _ _ _ hbad (hclaim.trans htruth))
        · have hvalid : ∀ i, body.residuals wires i = 0 := by simpa using hbad
          have hcurrent : claim = dot weights (body.outputs wires) := by
            rw [hclaim, htruth]
            simp [dot, hvalid]
          have hremaining : ¬ rest.AssertionsValid w := by
            intro hrest
            rcases hdoom with hfalse | hfalse
            · exact hfalse hcurrent
            · exact hfalse ⟨hvalid, hrest⟩
          exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail (Or.inr hremaining)))
      · by_cases hnext : t.nextValue pads = dot next wires
        · apply Or.inr ∘ Or.inl
          have h := LinearTerminal.affine_layer_reduction Q L wires K ml.point claim terminal
            t.cross t.scale t.messageA t.messageB t.alpha (t.terminalPads pads)
            (t.clearRounds pads) hclaim hrounds hrow hnext
          simpa only [← hterminal, Q, L, K, wires, t, LayerTranscript.clearA,
            LayerTranscript.clearB] using h
        · exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail (Or.inl hnext)))

theorem soundness_reduction {out input : ℕ} (circuit : Native.Circuit F out input)
    (m : Messages Pad circuit) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (proof circuit m (monomialWeights point))
      (dot (inputWeights circuit m (monomialWeights point)) w)) :
    OutputBad (circuit.eval w) point ∨ Bad circuit m w (monomialWeights point) pads 0 := by
  by_cases hzero : evaluate (circuit.eval w) point = 0
  · by_cases houtputs : circuit.eval w = 0
    · right
      apply reduction circuit m w (monomialWeights point) pads 0 haccept
      exact Or.inr (fun h => hfalse ⟨houtputs, h⟩)
    · exact Or.inl (output_reduction _ _ houtputs hzero)
  · right
    apply reduction circuit m w (monomialWeights point) pads 0 haccept
    rw [← evaluate_eq_dot]
    exact Or.inl (Ne.symm hzero)

/-- The exact linear compiler supplies the premise of native circuit reduction.
There is no side condition on the four committed terminal cells. -/
theorem compiled_circuit_reduction {out input nPublic nPrivate : ℕ}
    (circuit : Native.Circuit F out input) (m : Messages Pad circuit) (point : Fin out → F)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Constraints Pad F)
    (hbuild : buildConstraints (proof circuit m (monomialWeights point)) = some cs)
    (hrows : RowsHold (compile cs coordinate privateCoordinate
      (fun i => inputWeights circuit m (monomialWeights point) (index (.inl i))) publicInputs
      (fun i => inputWeights circuit m (monomialWeights point) (index (.inr i)))) witness)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    OutputBad (circuit.eval (circuitInputs index publicInputs privateCoordinate witness)) point ∨
      Bad circuit m (circuitInputs index publicInputs privateCoordinate witness)
        (monomialWeights point) (witness ∘ coordinate) 0 := by
  apply soundness_reduction circuit m _ point (witness ∘ coordinate) hfalse
  rw [input_sum]
  exact (compiled_iff_clear (proof circuit m (monomialWeights point)) cs hbuild
    coordinate privateCoordinate _ publicInputs _ witness).mp hrows

end Circuit
end LfzkV2.Linear
