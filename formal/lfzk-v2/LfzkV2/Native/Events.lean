import LfzkV2.Native.Soundness
import LfzkV2.ChallengeTests

/-!
# Native frontend challenge budget

The native reconstruction produces the existing `ChallengeTest` values, so
their finite-field root bounds are shared. Constants and linear terms introduce
no extra challenge slots or degree. This does not identify Rust's byte transcript
with a random oracle; that remains a separate composition obligation.
-/

namespace LfzkV2.Native

open SumcheckV2 Classical

variable {F Pad Slot : Type} [Field F]

noncomputable def assertionIndices {n : ℕ} (residuals : Fin n → F) : Finset (Fin n) :=
  Finset.univ.filter fun i => residuals i ≠ 0 ∧ ∀ j, i < j → residuals j = 0

noncomputable def assertionTests {n : ℕ}
    (incoming claim : F) (beta residuals : Fin n → F) : Tests F :=
  (assertionIndices residuals).toList.map fun i =>
    (.linear (assertionOffset incoming claim beta residuals i) (residuals i), beta i)

noncomputable def layerTests {n : ℕ} (q w : Cube n → F) (point : Fin n → F)
    (t : LfzkV2.LayerTranscript Pad Slot F) (pads : Pad → F) (claim K : F) : Tests F :=
  roundTests (claim - K) (truePolys q w point) (t.clearRounds pads) (List.ofFn point) ++
    [(.combine ⟨evaluate w point, evaluate q point, t.clearA pads, t.clearB pads⟩, t.alpha)]

namespace Circuit

noncomputable def layerTests : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube input → F) → (Cube out → F) → (Pad → F) → F → Tests F
  | _, _, .input, _, _, _, _, _ => []
  | _, _, .layer _ body rest, m, w, weights, pads, claim =>
      let Q := body.effectiveQuadratic weights m.1.beta
      let L := body.effectiveLinear weights m.1.beta
      let K := body.effectiveConstant weights
      let wires := rest.eval w
      assertionTests (dot weights (body.outputs wires)) claim m.1.beta (body.residuals wires) ++
        Native.layerTests (bindRightAffine Q L wires) wires m.1.point m.1.transcript pads claim K ++
        layerTests rest m.2 w (nextWeights Q (monomialWeights m.1.point) m.1.alpha) pads
          ((body.transcript weights m.1).nextValue pads)

noncomputable def tests {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (w : Cube input → F) (point : Fin out → F)
    (pads : Pad → F) : Tests F :=
  outputTests (circuit.eval w) point ++ circuit.layerTests m w (monomialWeights point) pads 0

end Circuit

end LfzkV2.Native
