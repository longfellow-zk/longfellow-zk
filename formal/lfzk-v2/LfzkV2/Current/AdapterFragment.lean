import LfzkV2.Current.AdapterCircuit

/-! Adding other quad fragments does not change the generated adapter's
values. The only restriction is public output-address disjointness. Inputs
may coincide, so the final input array remains shared. -/
noncomputable section
namespace LfzkV2.Current.Adapter.Circuit.Fragment
open Layered SumcheckV2
open scoped Classical

variable {F W : Type} [Field F]

/-- Other components' sparse terms and assertions in one dense global layer.
The stored certificate concerns addresses only; it assumes no output equation. -/
structure Extension {n out mid : ℕ} (output : Fin n ↪ Cube out) where
  terms : List (Layered.Term (Cube out) (Cube mid) F)
  disjoint : ∀ term ∈ terms, ∀ g, term.output ≠ output g
  checks : ℕ
  assertions : Fin checks → LfzkV2.Native.AssertionTerm (Cube mid)

def layer {n out mid : ℕ} (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) (other : Extension (F := F) (mid := mid) output) :
    LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin other.checks) F :=
  Layered.sparseLayer
    (((stream rows).map (Layered.Term.map output input)) ++ other.terms) other.assertions

/-- Only output addresses need separation; other fragments may read any of
these wires, including the same original Boolean inputs. -/
theorem layer_outputs {n out mid : ℕ} [Fintype W] (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) (other : Extension (F := F) (mid := mid) output)
    (w : Cube mid → F) (g : Fin n) :
    (layer rows input output other).outputs w (output g) = rowEval (rows g) (w ∘ input) := by
  rw [layer, Layered.sparseLayer_outputs, List.map_append, List.sum_append]
  have hz : (other.terms.map (Layered.Term.evaluated w (output g))).sum = 0 := by
    apply List.sum_eq_zero
    intro term hterm
    obtain ⟨term,ht,rfl⟩ := List.mem_map.mp hterm
    simp [Layered.Term.evaluated, other.disjoint term ht g]
  rw [hz, add_zero]
  have h := mappedLayer_outputs rows input output w g
  rw [mappedLayer, Layered.sparseLayer_outputs] at h
  exact h

variable {d q input final : ℕ} (layout : Layout)
  (output : Fin 2 ↪ Cube final)

/-- Actual terms of every other component, at the same layers as the
adapter. Its final entry may carry arbitrary other-component wires onward. -/
structure Others (layout : Layout) (d q input final : ℕ) (output : Fin 2 ↪ Cube final) where
  leaf : Extension (F := F) (mid := input) (layout.flat d q)
  pair : ∀ d q, Extension (F := F) (mid := layout.log d q) (layout.flat (half d) (half q))
  final : Extension (F := F) (mid := layout.log 1 1) output

def reduction {d q input : ℕ} (layout : Layout)
    (others : ∀ d q, Extension (F := F) (mid := layout.log d q)
      (layout.flat (half d) (half q))) (shape : Shape d q)
    (rest : Layered.Circuit F (layout.log d q) input) :
    Layered.Circuit F (layout.log 1 1) input :=
  match shape with
  | .root => rest
  | .pair next => reduction layout others next
      (.layer (others d q).checks
        (layer (pairRows d q) (layout.index d q) (layout.flat (half d) (half q)) (others d q)) rest)

theorem reduction_eval {d q input : ℕ} (layout : Layout)
    (others : ∀ d q, Extension (F := F) (mid := layout.log d q)
      (layout.flat (half d) (half q))) (shape : Shape d q)
    (rest : Layered.Circuit F (layout.log d q) input) (w : Cube input → F) (root : Wire 1 1) :
    (reduction layout others shape rest).eval w (layout.index 1 1 root) =
      roots shape (rest.eval w ∘ layout.index d q) root := by
  induction shape with
  | root => rfl
  | @pair d q next ih =>
      rw [reduction, ih, roots]
      apply congrArg (fun values => roots next values root)
      funext i
      change (layer (pairRows d q) (layout.index d q)
        (layout.flat (half d) (half q)) (others d q)).outputs (rest.eval w)
          (layout.index (half d) (half q) i) = _
      have he : layout.index (half d) (half q) i =
          layout.flat (half d) (half q) (wireIndex (half d) (half q) i) := by simp [Layout.flat]
      rw [he, layer_outputs]
      symm
      exact stream_outputs (pairRows d q) (rest.eval w ∘ layout.index d q) _

def body (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) : Layered.Circuit F final input :=
  .layer others.final.checks (layer (finalRows targets) (layout.index 1 1) output others.final)
    (reduction layout others.pair shape (.layer others.leaf.checks
      (layer (leafRows sources pads powers base masked) id (layout.flat d q) others.leaf) .input))

def build {out : ℕ} (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (carry : Cube out → Option (Cube final))
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) : Layered.Circuit F out input :=
  .entry 2 ⟨carry,output⟩ (body layout output shape others sources pads powers base masked targets)

theorem body_eval (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) (w : Cube input → F) (tree : Fin 2) :
    (body layout output shape others sources pads powers base masked targets).eval w (output tree) =
      eval shape sources pads powers base masked targets w tree := by
  simp only [body, Layered.Circuit.eval, layer_outputs, eval, stream_outputs]
  congr 1
  funext root
  rw [Function.comp_apply, reduction_eval]
  apply congrArg (fun values => roots shape values root)
  funext i
  change (layer (leafRows sources pads powers base masked) id
    (layout.flat d q) others.leaf).outputs w (layout.index d q i) =
      leafState sources pads powers base masked w i
  have he : layout.index d q i = layout.flat d q (wireIndex d q i) := by simp [Layout.flat]
  rw [he, layer_outputs]
  symm
  exact stream_outputs (leafRows sources pads powers base masked) w _

theorem build_satisfies {out : ℕ} (shape : Shape d q)
    (others : Others (F := F) layout d q input final output) (carry : Cube out → Option (Cube final))
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) (w : Cube input → F)
    (h : (build layout output shape others carry sources pads powers base masked targets).Satisfies w) :
    Satisfies shape sources pads powers base masked targets w := by
  intro tree
  have hz := h.1 tree
  change (body layout output shape others sources pads powers base masked targets).eval w (output tree) = 0 at hz
  rwa [body_eval] at hz

/-- Upper layers of deeper components are ordinary circuit constructors.
Their satisfaction includes satisfaction of the existing lower circuit. -/
inductive Above (F : Type) : ℕ → ℕ → Type where
  | hole {n : ℕ} : Above F n n
  | entry {out mid base : ℕ} (checks : ℕ) (mapping : Layered.Entry (Cube out) (Cube mid) checks)
      (rest : Above F mid base) : Above F out base
  | layer {out mid base : ℕ} (checks : ℕ)
      (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin checks) F)
      (rest : Above F mid base) : Above F out base

def Above.plug {out mid input : ℕ} : Above F out mid → Layered.Circuit F mid input → Layered.Circuit F out input
  | .hole, rest => rest
  | .entry checks mapping next, rest => .entry checks mapping (next.plug rest)
  | .layer checks body next, rest => .layer checks body (next.plug rest)

theorem Above.satisfies {out mid input : ℕ} (above : Above F out mid)
    (rest : Layered.Circuit F mid input) (w : Cube input → F)
    (h : (above.plug rest).Satisfies w) : rest.Satisfies w := by
  induction above with
  | hole => exact h
  | entry checks mapping next ih => exact ih rest h.2
  | layer checks body next ih => exact ih rest h.2

/-- Arbitrary other fragments and deeper upper layers cannot remove the two
adapter checks. This supplies the application's product equations directly
from satisfaction of the complete constructed layered circuit. -/
theorem full_product_check {p out upper : ℕ} [Fact p.Prime] [CharP F 2]
    (shape : Shape d q) (others : Others (F := F) layout d q input final output)
    (carry : Cube out → Option (Cube final)) (above : Above F upper out)
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (generator : Fˣ) (weights : Fin d → ZMod p) (target : ZMod p)
    (alpha : Fin 2 → ZMod p) (masked : Fin 2 → Fin q → Bool) (bits : Cube input → Bool)
    (h : (above.plug (build layout output shape others carry sources pads
      (fun tree i => generator^(alpha tree*weights i).val) (generator^(-(p : ℤ))) masked
      (fun tree => generator^(alpha tree*target).val))).Satisfies (bitValue ∘ bits)) :
    let quotient := fun tree => Tree.binaryValue
      (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i))
    (∀ tree, quotient tree < 2^q) ∧ ∀ tree,
      Adapter.ProductCheck generator weights (bits ∘ sources) target (alpha tree) (quotient tree) :=
  satisfies_product_check shape sources pads generator weights target alpha masked bits
    (build_satisfies layout output shape others carry sources pads _ _ masked _ _
      (above.satisfies _ _ h))

end LfzkV2.Current.Adapter.Circuit.Fragment
