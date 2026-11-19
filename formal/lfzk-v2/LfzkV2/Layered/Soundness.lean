import LfzkV2.Layered.Circuit

/-!
# Layered sumcheck with independent zero-output entries

The reduction includes every layer, assertion, affine correction, and the
entry checks at every depth. A false accepted circuit encounters a round, terminal,
combination, assertion, or entry bad event. Candidate products are arbitrary
throughout this argument.

Tests that read one challenge answer are reported only where the earlier
ones cannot cover them: an entry's failure is reported only when the layer
it enters passes its assertions, and a combination failure only when the
checks that follow it in the same answer all pass. Otherwise the later
check of that answer is false and the reduction continues there, so the
tests of one answer form a single affine cancellation.
-/

namespace LfzkV2.Layered

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

namespace Circuit

/-- The assertion count of a top layer, and zero for the other forms. -/
def layerWidth : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .layer a _ _ => a
  | _, _, _ => 0

/-- A top layer's assertion residuals; the other forms check none. -/
noncomputable def layerResiduals : {out input : ℕ} → (circuit : Circuit F out input) →
    (Cube input → F) → Fin circuit.layerWidth → F
  | _, _, .layer _ body rest, w => body.residuals (rest.eval w)
  | _, _, .input, _ => Fin.elim0
  | _, _, .entry .., _ => Fin.elim0

/-- The residuals checked with the answer that opens `circuit`: an entry's
fresh outputs, then the assertions of the layer it enters. -/
def headWidth : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry n _ rest => n + rest.layerWidth
  | _, _, .layer a _ _ => a

noncomputable def headResiduals : {out input : ℕ} → (circuit : Circuit F out input) →
    (Cube input → F) → Fin circuit.headWidth → F
  | _, _, .input, _ => Fin.elim0
  | _, _, .entry _ e rest, w => Fin.append (e.residuals (rest.eval w)) (rest.layerResiduals w)
  | _, _, .layer _ body rest, w => body.residuals (rest.eval w)

/-- An entry is charged at its own test only if the layer it enters passes. -/
noncomputable def entryResiduals {out next input n : ℕ}
    (e : Entry (Cube out) (Cube next) n) (rest : Circuit F next input) (w : Cube input → F) :
    Fin n → F :=
  if ∀ i, rest.layerResiduals w i = 0 then e.residuals (rest.eval w) else 0

theorem not_satisfies_of_layerResiduals {out input : ℕ} (circuit : Circuit F out input)
    (w : Cube input → F) (h : ¬ ∀ i, circuit.layerResiduals w i = 0) : ¬ circuit.Satisfies w := by
  cases circuit with
  | input => exact (h fun i => Fin.elim0 i).elim
  | entry => exact (h fun i => Fin.elim0 i).elim
  | layer a body rest => exact fun hs => h hs.1

theorem not_satisfies_of_headResiduals {out input : ℕ} (circuit : Circuit F out input)
    (w : Cube input → F) (h : ¬ ∀ i, circuit.headResiduals w i = 0) : ¬ circuit.Satisfies w := by
  cases circuit with
  | input => exact (h fun i => Fin.elim0 i).elim
  | entry n e rest =>
      intro hs
      apply h
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa [headResiduals] using hs.1 j
      · have hl : ∀ i, rest.layerResiduals w i = 0 := by
          by_contra hl
          exact not_satisfies_of_layerResiduals rest w hl hs.2
        simpa [headResiduals] using hl j
  | layer a body rest => exact fun hs => h hs.1

noncomputable def Bad : {out input : ℕ} → (circuit : Circuit F out input) →
    Messages Pad circuit → (Cube input → F) → (Cube out → F) → (Pad → F) → F → Prop
  | _, _, .input, _, _, _, _, _ => False
  | _, _, .entry _ e rest, m, w, weights, pads, claim =>
      AssertionBad (dot weights (e.previous (rest.eval w))) claim m.1 (entryResiduals e rest w) ∨
        Bad rest m.2 w (e.weights weights m.1) pads claim
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
          ((∀ i, rest.headResiduals w i = 0) ∧
            BadCombineEvent (evaluate wires m.1.point) (evaluate q m.1.point)
              (t.clearA pads) (t.clearB pads) t.alpha)) ∨
        Bad rest m.2 w (nextWeights Q (monomialWeights m.1.point) m.1.alpha) pads
          (t.nextValue pads)

theorem reduction {out input : ℕ} (circuit : Circuit F out input)
    (m : Messages Pad circuit) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F)
    (haccept : Linear.ClearAccepts pads claim (proof circuit m weights)
      (dot (inputWeights circuit m weights) w))
    (hdoom : claim ≠ dot weights (circuit.eval w) ∨ ¬ circuit.Satisfies w) :
    Bad circuit m w weights pads claim := by
  induction circuit generalizing claim with
  | input =>
      rcases hdoom with hfalse | hfalse
      · exact (hfalse haccept).elim
      · exact (hfalse trivial).elim
  | entry n e rest ih =>
      by_cases hnext : claim = dot (e.weights weights m.1) (rest.eval w)
      · by_cases hbad : ∃ i, e.residuals (rest.eval w) i ≠ 0
        · by_cases hlayer : ∀ i, rest.layerResiduals w i = 0
          · apply Or.inl
            simpa only [entryResiduals, hlayer, implies_true, ↓reduceIte] using
              e.cancellation weights m.1 (rest.eval w) claim hbad hnext
          · exact Or.inr (ih m.2 w (e.weights weights m.1) claim haccept
              (Or.inr (not_satisfies_of_layerResiduals rest w hlayer)))
        · have hvalid : ∀ i, e.residuals (rest.eval w) i = 0 := by simpa using hbad
          have hcurrent : claim = dot weights (e.previous (rest.eval w)) :=
            hnext.trans (e.dot_weights_of_zero weights m.1 (rest.eval w) hvalid)
          have hrest : ¬ rest.Satisfies w := by
            intro h
            rcases hdoom with hf | hf
            · exact hf hcurrent
            · exact hf ⟨hvalid,h⟩
          exact Or.inr (ih m.2 w (e.weights weights m.1) claim haccept (Or.inr hrest))
      · exact Or.inr (ih m.2 w (e.weights weights m.1) claim haccept (Or.inl hnext))
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
          have hremaining : ¬ rest.Satisfies w := by
            intro hrest
            rcases hdoom with hfalse | hfalse
            · exact hfalse hcurrent
            · exact hfalse ⟨hvalid, hrest⟩
          exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail (Or.inr hremaining)))
      · by_cases hnext : t.nextValue pads = dot next wires
        · have h := LinearTerminal.affine_layer_reduction Q L wires K ml.point claim terminal
            t.cross t.scale t.messageA t.messageB t.alpha (t.terminalPads pads)
            (t.clearRounds pads) hclaim hrounds hrow hnext
          rcases h with hround | hterm | hcombine
          · apply Or.inr ∘ Or.inl ∘ Or.inl
            simpa only [Q, L, K, wires, t] using hround
          · apply Or.inr ∘ Or.inl ∘ Or.inr ∘ Or.inl
            simpa only [← hterminal, Q, L, K, wires, t] using hterm
          · by_cases hhead : ∀ i, rest.headResiduals w i = 0
            · apply Or.inr ∘ Or.inl ∘ Or.inr ∘ Or.inr
              exact ⟨hhead, by simpa only [Q, L, wires, t, Linear.LayerTranscript.clearA,
                Linear.LayerTranscript.clearB] using hcombine⟩
            · exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail
                (Or.inr (not_satisfies_of_headResiduals rest w hhead))))
        · exact Or.inr (Or.inr (ih mr w next (t.nextValue pads) htail (Or.inl hnext)))

/-- All zero-output checks occur at their entry boundaries. Starting from
zero weights and claim therefore needs no initial output-evaluation event. -/
theorem soundness_reduction {out input : ℕ} (circuit : Circuit F out input)
    (m : Messages Pad circuit) (w : Cube input → F) (pads : Pad → F)
    (hfalse : ¬ circuit.Satisfies w) (haccept : circuit.Accepts m w pads) :
    Bad circuit m w 0 pads 0 :=
  reduction circuit m w 0 pads 0 haccept (Or.inr hfalse)

/-- The unchanged affine constraint compiler authenticates the one global
input claim. Entries introduce neither new commitment cells nor extra rows. -/
theorem compiled_circuit_reduction {out input nPublic nPrivate : ℕ}
    (circuit : Circuit F out input) (m : Messages Pad circuit)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Linear.Constraints Pad F)
    (hbuild : Linear.buildConstraints (proof circuit m 0) = some cs)
    (hrows : RowsHold (Linear.compile cs coordinate privateCoordinate
      (fun i => inputWeights circuit m 0 (index (.inl i))) publicInputs
      (fun i => inputWeights circuit m 0 (index (.inr i)))) witness)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    Bad circuit m (circuitInputs index publicInputs privateCoordinate witness)
      0 (witness ∘ coordinate) 0 := by
  apply soundness_reduction circuit m _ (witness ∘ coordinate) hfalse
  change Linear.ClearAccepts _ _ _ _
  rw [input_sum]
  exact (Linear.compiled_iff_clear (proof circuit m 0) cs hbuild
    coordinate privateCoordinate _ publicInputs _ witness).mp hrows

end Circuit
end LfzkV2.Layered
