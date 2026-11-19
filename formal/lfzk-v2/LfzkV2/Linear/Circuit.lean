import LfzkV2.Linear.Constraints
import LfzkV2.Native.Circuit

/-!
# Linear-terminal messages for the native circuit

Circuit semantics, assertion residuals, and the public `Q`, `L`, `K` tensors
are shared with `Native.Circuit`. Only protocol messages change. Terminal pad
identifiers are ordinary members of `Pad`; no special product-slot type is
part of this frontend.
-/

namespace LfzkV2.Linear

open SumcheckV2

variable {F Pad : Type} [Field F]

structure LayerMessages (Pad F : Type) (rounds assertions : ℕ) where
  roundMessages : Fin rounds → RoundPoly F
  roundPads : Fin rounds → Pad × Pad
  point : Fin rounds → F
  beta : Fin assertions → F
  cross : F
  scale : F
  messageA : F
  messageB : F
  padA : Pad
  padB : Pad
  padAB : Pad
  padD : Pad
  alpha : F

noncomputable def LayerMessages.transcript {out n a : ℕ}
    (m : LayerMessages Pad F n a)
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin a) F)
    (weights : Cube out → F) : LayerTranscript Pad F where
  rounds := List.ofFn fun i => (m.roundMessages i, m.roundPads i)
  challenges := List.ofFn m.point
  cross := m.cross
  scale := m.scale
  messageA := m.messageA
  messageB := m.messageB
  padA := m.padA
  padB := m.padB
  padAB := m.padAB
  padD := m.padD
  alpha := m.alpha
  constant := body.effectiveConstant weights
  linear := evaluate (body.effectiveLinear weights m.beta) m.point

namespace Circuit

abbrev Messages (Pad : Type) : {out input : ℕ} → Native.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest => LayerMessages Pad F mid a × Messages Pad rest

noncomputable def proof : {out input : ℕ} → (circuit : Native.Circuit F out input) →
    Messages Pad circuit → (Cube out → F) → List (LayerTranscript Pad F)
  | _, _, .input, _, _ => []
  | _, _, .layer _ body rest, m, weights =>
      m.1.transcript body weights :: proof rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

noncomputable def inputWeights : {out input : ℕ} → (circuit : Native.Circuit F out input) →
    Messages Pad circuit → (Cube out → F) → Cube input → F
  | _, _, .input, _, weights => weights
  | _, _, .layer _ body rest, m, weights =>
      inputWeights rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

end Circuit

end LfzkV2.Linear
