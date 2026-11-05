import LfzkV2.Native.Constraints
import LfzkV2.Program
import SumcheckV2.Affine

/-!
# The native three-stream circuit

Ordinary quadratic, linear, and constant terms have separate tensors. Assertion
occurrences are either quadratic or linear and receive independent coefficients
that replace the entire output-weighted coefficient. The sparse Rust traversal
is represented by sums of these tensors; repeated occurrences are retained.
-/

namespace LfzkV2.Native

open SumcheckV2 Classical

variable {F Wire Output Assertion : Type} [Field F]
variable [Fintype Wire] [Fintype Output] [Fintype Assertion]

inductive AssertionTerm (Wire : Type) where
  | quadratic (left right : Wire)
  | linear (wire : Wire)

namespace AssertionTerm

noncomputable def quadraticKernel (term : AssertionTerm Wire) (l r : Wire) : F :=
  match term with
  | .quadratic x y => if l = x ∧ r = y then 1 else 0
  | .linear _ => 0

noncomputable def linearKernel (term : AssertionTerm Wire) (l : Wire) : F :=
  match term with
  | .quadratic _ _ => 0
  | .linear x => if l = x then 1 else 0

def residual (term : AssertionTerm Wire) (w : Wire → F) : F :=
  match term with
  | .quadratic l r => w l * w r
  | .linear l => w l

theorem residual_eq (term : AssertionTerm Wire) (w : Wire → F) :
    LfzkV2.quadratic term.quadraticKernel w + dot term.linearKernel w = term.residual w := by
  cases term <;> simp [LfzkV2.quadratic, dot, quadraticKernel, linearKernel, residual, ite_and]

end AssertionTerm

theorem dot_add_left (a b w : Wire → F) :
    dot (fun i => a i + b i) w = dot a w + dot b w := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_add_right (w a b : Wire → F) :
    dot w (fun i => a i + b i) = dot w a + dot w b := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_weighted_sum (weights : Output → F) (L : Output → Wire → F) (w : Wire → F) :
    dot (fun l => ∑ g, weights g * L g l) w = dot weights (fun g => dot (L g) w) := by
  simp only [dot, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem affine_truth (Q : Wire → Wire → F) (L w : Wire → F) :
    dot (bindRightAffine Q L w) w = quadratic Q w + dot L w := by
  rw [quadratic_eq_dot, ← dot_add_left]
  rfl

structure CircuitLayer (Output Wire Assertion F : Type) where
  quadratic : Output → Wire → Wire → F
  linear : Output → Wire → F
  constant : Output → F
  assertions : Assertion → AssertionTerm Wire

namespace CircuitLayer

def outputs (layer : CircuitLayer Output Wire Assertion F) (w : Wire → F) : Output → F :=
  fun g => LfzkV2.quadratic (layer.quadratic g) w + dot (layer.linear g) w + layer.constant g

def residuals (layer : CircuitLayer Output Wire Assertion F) (w : Wire → F) : Assertion → F :=
  fun a => (layer.assertions a).residual w

noncomputable def effectiveQuadratic (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (l r : Wire) : F :=
  (∑ g, weights g * layer.quadratic g l r) +
    ∑ a, beta a * (layer.assertions a).quadraticKernel l r

noncomputable def effectiveLinear (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (l : Wire) : F :=
  (∑ g, weights g * layer.linear g l) +
    ∑ a, beta a * (layer.assertions a).linearKernel l

def effectiveConstant (layer : CircuitLayer Output Wire Assertion F) (weights : Output → F) : F :=
  dot weights layer.constant

/-- No assertion-validity premise: invalid linear and quadratic assertions both
contribute their independently weighted residuals to the true incoming claim. -/
theorem effective_truth (layer : CircuitLayer Output Wire Assertion F)
    (weights : Output → F) (beta : Assertion → F) (w : Wire → F) :
    dot (bindRightAffine (layer.effectiveQuadratic weights beta)
      (layer.effectiveLinear weights beta) w) w + layer.effectiveConstant weights =
      dot weights (layer.outputs w) + dot beta (layer.residuals w) := by
  rw [affine_truth]
  unfold effectiveQuadratic effectiveLinear effectiveConstant
  rw [quadratic_add, quadratic_weighted_sum, quadratic_weighted_sum,
    dot_add_left, dot_weighted_sum, dot_weighted_sum]
  have hassert :
      dot beta (fun a => LfzkV2.quadratic (layer.assertions a).quadraticKernel w) +
        dot beta (fun a => dot (layer.assertions a).linearKernel w) =
      dot beta (layer.residuals w) := by
    rw [← dot_add_right]
    congr 1
    funext a
    exact AssertionTerm.residual_eq (layer.assertions a) w
  have hordinary :
      dot weights (fun g => LfzkV2.quadratic (layer.quadratic g) w) +
        dot weights (fun g => dot (layer.linear g) w) + dot weights layer.constant =
      dot weights (layer.outputs w) := by
    simp [dot, outputs, mul_add, Finset.sum_add_distrib]
  linear_combination hordinary + hassert

noncomputable def transcript {n a : ℕ} {Pad Slot : Type}
    (layer : CircuitLayer Output (Cube n) (Fin a) F) (weights : Output → F)
    (m : LfzkV2.LayerMessages Pad Slot F n a) : LayerTranscript Pad Slot F :=
  ⟨m.transcript, layer.effectiveConstant weights,
    evaluate (layer.effectiveLinear weights m.beta) m.point⟩

end CircuitLayer

inductive Circuit (F : Type) : ℕ → ℕ → Type where
  | input {n : ℕ} : Circuit F n n
  | layer {out mid input : ℕ} (assertions : ℕ)
      (body : CircuitLayer (Cube out) (Cube mid) (Fin assertions) F)
      (rest : Circuit F mid input) : Circuit F out input

namespace Circuit

variable {Pad Slot : Type}

abbrev Messages (Pad Slot : Type) : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) a _ rest =>
      LfzkV2.LayerMessages Pad Slot F mid a × Messages Pad Slot rest

noncomputable def eval : {out input : ℕ} → Circuit F out input → (Cube input → F) → Cube out → F
  | _, _, .input, w => w
  | _, _, .layer _ body rest, w => body.outputs (eval rest w)

def AssertionsValid : {out input : ℕ} → Circuit F out input → (Cube input → F) → Prop
  | _, _, .input, _ => True
  | _, _, .layer _ body rest, w =>
      (∀ i, body.residuals (eval rest w) i = 0) ∧ AssertionsValid rest w

def Satisfies {out input : ℕ} (circuit : Circuit F out input) (w : Cube input → F) : Prop :=
  circuit.eval w = 0 ∧ circuit.AssertionsValid w

/-- Corrections are derived here from the trusted circuit. They are absent from
`Messages`, so a proof cannot choose them independently of the reconstruction. -/
noncomputable def proof : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube out → F) → List (LayerTranscript Pad Slot F)
  | _, _, .input, _, _ => []
  | _, _, .layer _ body rest, m, weights =>
      body.transcript weights m.1 :: proof rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

noncomputable def inputWeights : {out input : ℕ} → (circuit : Circuit F out input) →
    circuit.Messages Pad Slot → (Cube out → F) → Cube input → F
  | _, _, .input, _, weights => weights
  | _, _, .layer _ body rest, m, weights =>
      inputWeights rest m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha)

end Circuit

end LfzkV2.Native
