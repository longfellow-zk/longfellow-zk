import LfzkV2.Layered.Circuit

/-!
# Quad fragments describe sparse terms, not wire storage

Every contraction below reads the same global witness or monomial array.
Local indices are translated only while visiting a term. Flattening the
fragments and traversing them separately give identical coefficients, even
when input maps overlap. The shared-input boundary is therefore covered by
the same statements as disjoint intermediate offsets.
-/

namespace LfzkV2.Layered

open SumcheckV2
open scoped Classical

variable {F W O : Type} [Field F]

inductive Term (O W F : Type) where
  | quadratic (output : O) (left right : W) (coefficient : F)
  | linear (output : O) (input : W) (coefficient : F)
  | constant (output : O) (coefficient : F)

namespace Term

variable {W' O' : Type}

def map (output : O → O') (wire : W → W') : Term O W F → Term O' W' F
  | .quadratic g l r k => .quadratic (output g) (wire l) (wire r) k
  | .linear g l k => .linear (output g) (wire l) k
  | .constant g k => .constant (output g) k

def output : Term O W F → O
  | .quadratic g _ _ _ => g
  | .linear g _ _ => g
  | .constant g _ => g

def value (w : W → F) : Term O W F → F
  | .quadratic _ l r k => k*w l*w r
  | .linear _ l k => k*w l
  | .constant _ k => k

theorem value_map (output : O → O') (wire : W → W') (w : W' → F) (term : Term O W F) :
    (term.map output wire).value w = term.value (w ∘ wire) := by
  cases term <;> rfl

noncomputable def evaluated (w : W → F) (g : O) (term : Term O W F) : F :=
  if term.output = g then term.value w else 0

noncomputable def left (a : O → F) (w : W → F) (i : W) : Term O W F → F
  | .quadratic g l r k => if l = i then a g*k*w r else 0
  | .linear g l k => if l = i then a g*k else 0
  | .constant _ _ => 0

noncomputable def right (a : O → F) (m : W → F) (i : W) : Term O W F → F
  | .quadratic g l r k => if r = i then a g*k*m l else 0
  | .linear _ _ _ => 0
  | .constant _ _ => 0

def constantPart (a : O → F) : Term O W F → F
  | .constant g k => a g*k
  | _ => 0

def linearPart (a : O → F) (m : W → F) : Term O W F → F
  | .linear g l k => a g*k*m l
  | _ => 0

end Term

/-- Only sparse terms and coordinate maps are local to a fragment. In Rust,
these maps are contiguous ranges into one dense array; input ranges coincide
at the common input boundary. -/
structure QuadFragment (O W F : Type) where
  outputs : ℕ
  inputs : ℕ
  outputIndex : Fin outputs → O
  inputIndex : Fin inputs → W
  terms : List (Term (Fin outputs) (Fin inputs) F)

def QuadFragment.globalTerms (fragment : QuadFragment O W F) : List (Term O W F) :=
  fragment.terms.map (Term.map fragment.outputIndex fragment.inputIndex)

def flatten (fragments : List (QuadFragment O W F)) : List (Term O W F) :=
  fragments.flatMap QuadFragment.globalTerms

/-- Any additive sparse contraction commutes with fragment traversal. There
is no disjointness hypothesis: all contributions to a shared input add. -/
theorem contraction_flatten (fragments : List (QuadFragment O W F)) (contribution : Term O W F → F) :
    ((flatten fragments).map contribution).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map contribution).sum).sum := by
  induction fragments with
  | nil => rfl
  | cons fragment rest ih =>
      simpa [flatten, List.map_append, List.sum_append] using ih

theorem evaluate_flatten (fragments : List (QuadFragment O W F)) (w : W → F) (g : O) :
    ((flatten fragments).map (Term.evaluated w g)).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map (Term.evaluated w g)).sum).sum :=
  contraction_flatten fragments _

theorem bind_right_flatten (fragments : List (QuadFragment O W F)) (a : O → F) (w : W → F) (l : W) :
    ((flatten fragments).map (Term.left a w l)).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map (Term.left a w l)).sum).sum :=
  contraction_flatten fragments _

theorem bind_left_flatten (fragments : List (QuadFragment O W F)) (a : O → F) (m : W → F) (r : W) :
    ((flatten fragments).map (Term.right a m r)).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map (Term.right a m r)).sum).sum :=
  contraction_flatten fragments _

theorem constants_flatten (fragments : List (QuadFragment O W F)) (a : O → F) :
    ((flatten fragments).map (Term.constantPart a)).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map (Term.constantPart a)).sum).sum :=
  contraction_flatten fragments _

theorem linear_correction_flatten (fragments : List (QuadFragment O W F)) (a : O → F) (m : W → F) :
    ((flatten fragments).map (Term.linearPart a m)).sum =
      (fragments.map fun fragment => (fragment.globalTerms.map (Term.linearPart a m)).sum).sum :=
  contraction_flatten fragments _

/-- A single global monomial array is reused by every fragment. The affine
transition is performed once after their sparse right coefficients add. -/
theorem transition_flatten (fragments : List (QuadFragment O W F)) (a : O → F)
    (m : W → F) (alpha : F) (r : W) :
    m r + alpha*((flatten fragments).map (Term.right a m r)).sum =
      m r + alpha*(fragments.map fun fragment =>
        (fragment.globalTerms.map (Term.right a m r)).sum).sum := by
  rw [bind_left_flatten]

end LfzkV2.Layered
