import LfzkV2.Layered.Entry
import LfzkV2.Linear.Soundness

/-!
# A layered circuit with zero-output entries

There is one dense wire array at each ordinary layer. Quad fragments are a
sparse description of that layer's public quadratic, linear, and constant
tensors. An `entry` changes only the indexing and output weights, adding no
sumcheck rounds, terminal factors, pads, or messages. Circuits of different
depths enter when their outputs meet the current layer.
-/

namespace LfzkV2.Layered

open SumcheckV2

variable {F Pad : Type} [Field F]

inductive Circuit (F : Type) : ℕ → ℕ → Type where
  | input {n : ℕ} : Circuit F n n
  | entry {out next input : ℕ} (checks : ℕ) (mapping : Entry (Cube out) (Cube next) checks)
      (rest : Circuit F next input) : Circuit F out input
  | layer {out mid input : ℕ} (assertions : ℕ)
      (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
      (rest : Circuit F mid input) : Circuit F out input

namespace Circuit

abbrev Messages (Pad : Type) : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .entry checks _ rest => (Fin checks → F) × Messages Pad rest
  | _, _, .layer (mid := mid) a _ rest => Linear.LayerMessages Pad F mid a × Messages Pad rest

noncomputable def eval : {out input : ℕ} → Circuit F out input → (Cube input → F) → Cube out → F
  | _, _, .input, w => w
  | _, _, .entry _ e rest, w => e.previous (rest.eval w)
  | _, _, .layer _ body rest, w => body.outputs (rest.eval w)

def Satisfies : {out input : ℕ} → Circuit F out input → (Cube input → F) → Prop
  | _, _, .input, _ => True
  | _, _, .entry _ e rest, w => (∀ i, e.residuals (rest.eval w) i = 0) ∧ rest.Satisfies w
  | _, _, .layer _ body rest, w => (∀ i, body.residuals (rest.eval w) i = 0) ∧ rest.Satisfies w

noncomputable def proof : {out input : ℕ} → (circuit : Circuit F out input) →
    Messages Pad circuit → (Cube out → F) → List (Linear.LayerTranscript Pad F)
  | _, _, .input, _, _ => []
  | _, _, .entry _ e rest, m, weights => proof rest m.2 (e.weights weights m.1)
  | _, _, .layer _ body rest, m, weights =>
      m.1.transcript body weights :: proof rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

noncomputable def inputWeights : {out input : ℕ} → (circuit : Circuit F out input) →
    Messages Pad circuit → (Cube out → F) → Cube input → F
  | _, _, .input, _, weights => weights
  | _, _, .entry _ e rest, m, weights => inputWeights rest m.2 (e.weights weights m.1)
  | _, _, .layer _ body rest, m, weights =>
      inputWeights rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

/-- The public zero-output statement is represented by entries, including the
scalar and zero-layer cases. No separate initial monomial-output check occurs. -/
noncomputable def Accepts {out input : ℕ} (circuit : Circuit F out input)
    (m : Messages Pad circuit) (w : Cube input → F) (pads : Pad → F) : Prop :=
  Linear.ClearAccepts pads 0 (circuit.proof m 0) (dot (circuit.inputWeights m 0) w)

def layers : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry _ _ rest => rest.layers
  | _, _, .layer _ _ rest => 1 + rest.layers

def rounds : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry _ _ rest => rest.rounds
  | _, _, .layer (mid := mid) _ _ rest => mid + rest.rounds

def entryBlocks : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry n _ rest => min 1 n + rest.entryBlocks
  | _, _, .layer _ _ rest => rest.entryBlocks

def ordinaryBudget : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry n _ rest => min 1 n + rest.ordinaryBudget
  | _, _, .layer (mid := mid) n _ rest => min 1 n + 2*mid + 1 + rest.ordinaryBudget

end Circuit
end LfzkV2.Layered
