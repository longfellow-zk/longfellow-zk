import LfzkV2.Native.Circuit
import LfzkV2.Inputs

/-!
# Native affine circuit soundness

The circuit reconstructs both public corrections and all input weights. An
accepted false witness must encounter an output, assertion, quadratic-round,
or linear-combination bad event. The existing root bounds apply unchanged.
This is the deterministic frontend reduction, before the packed commitment
adapter and adaptive Fiat–Shamir composition.
-/

namespace LfzkV2.Native.Circuit

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

noncomputable def Bad : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube input → F) → (Cube out → F) → (Pad → F) → F → Prop
  | _, _, .input, _, _, _, _, _ => False
  | _, _, .layer _ body rest, m, w, weights, pads, claim =>
      let Q := body.effectiveQuadratic weights m.1.beta
      let L := body.effectiveLinear weights m.1.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      let q := bindRightAffine Q L wires
      let t := m.1.transcript
      AssertionBad (dot weights (body.outputs wires)) claim m.1.beta (body.residuals wires) ∨
        (multi_round_bad_event (claim - K) (truePolys q wires m.1.point)
            (t.clearRounds pads) (List.ofFn m.1.point) ∨
          BadCombineEvent (evaluate wires m.1.point) (evaluate q m.1.point)
            (t.clearA pads) (t.clearB pads) t.alpha) ∨
        Bad rest m.2 w (nextWeights Q (monomialWeights m.1.point) m.1.alpha) pads
          ((body.transcript weights m.1).nextValue pads)

/-- Propagation includes violated assertions even if every circuit output is zero.
The true incoming scalar is derived from the three streams, without assuming
that any assertion is valid. -/
theorem reduction {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (haccept : ClearAccepts pads claim (circuit.proof m weights)
      (dot (circuit.inputWeights m weights) w))
    (hdoom : claim ≠ dot weights (circuit.eval w) ∨ ¬ circuit.AssertionsValid w) :
    circuit.Bad m w weights pads claim := by
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
      let t := body.transcript weights ml
      rcases haccept with ⟨hterminal, htail⟩
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
        · exact Or.inr (Or.inl (affine_layer_reduction Q L wires K ml.point claim
            (ml.transcript.clearA pads) (ml.transcript.clearB pads) ml.alpha
            (ml.transcript.clearRounds pads) hclaim hterminal hnext))
        · exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail (Or.inl hnext)))

/-- Current native sumcheck endpoint, including the initial all-zero output claim. -/
theorem soundness_reduction {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) (hfalse : ¬ circuit.Satisfies w)
    (haccept : ClearAccepts pads 0 (circuit.proof m (monomialWeights point))
      (dot (circuit.inputWeights m (monomialWeights point)) w)) :
    OutputBad (circuit.eval w) point ∨ circuit.Bad m w (monomialWeights point) pads 0 := by
  by_cases hzero : evaluate (circuit.eval w) point = 0
  · by_cases houtputs : circuit.eval w = 0
    · right
      apply circuit.reduction m w (monomialWeights point) pads 0 haccept
      exact Or.inr (fun h => hfalse ⟨houtputs, h⟩)
    · exact Or.inl (output_reduction _ _ houtputs hzero)
  · right
    apply circuit.reduction m w (monomialWeights point) pads 0 haccept
    rw [← evaluate_eq_dot]
    exact Or.inl (Ne.symm hzero)

/-- The source input equation and the layer rows produced by the shared sparse
compiler imply the native circuit reduction. A packed backend must authenticate
that source equation through its separate packing theorem. -/
theorem compiled_circuit_reduction {out input nPublic nPrivate : ℕ}
    (circuit : Circuit F out input) (m : circuit.Messages Pad Slot) (point : Fin out → F)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Constraints Pad Slot F)
    (hbuild : Native.buildConstraints (circuit.proof m (monomialWeights point)) = some cs)
    (hproducts : ProductsHold cs coordinate witness)
    (hrows : RowsHold (compile cs coordinate privateCoordinate
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inl i))) publicInputs
      (fun i => circuit.inputWeights m (monomialWeights point) (index (.inr i)))) witness)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    OutputBad (circuit.eval (circuitInputs index publicInputs privateCoordinate witness)) point ∨
      circuit.Bad m (circuitInputs index publicInputs privateCoordinate witness)
        (monomialWeights point) (witness ∘ coordinate) 0 := by
  apply circuit.soundness_reduction m _ point (witness ∘ coordinate) hfalse
  rw [input_sum]
  exact (Native.compiled_iff_clear (circuit.proof m (monomialWeights point)) cs hbuild
    coordinate privateCoordinate _ publicInputs _ witness hproducts).mp hrows

end LfzkV2.Native.Circuit
