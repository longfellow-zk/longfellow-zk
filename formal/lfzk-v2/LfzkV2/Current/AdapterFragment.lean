import LfzkV2.Current.AdapterLeaves

/-! Place the fixed adapter fragment in the joint layered circuit. The hash
component is deeper, and at every adapter layer its sparse fragments share
the global wire arrays. Adding other fragments does not change the adapter's
values; the only restriction here is public output-address disjointness.
The adapter's first reduction reads its virtual leaves directly from the
shared input array; it has no leaf layer and no challenge coefficient. -/
noncomputable section
namespace LfzkV2.Current.Adapter.Fragment
open Layered SumcheckV2 Adapter.Circuit Adapter.ProductTree
open scoped Classical

variable {F W : Type} [Field F]

/-- Every intermediate adapter layer has its own dense wire array. These
public injections specify its ordinary indexing; no semantic equality is
stored in the layout. -/
structure Layout where
  log : ℕ → ℕ
  index : ∀ n, Wire n ↪ Cube (log n)

def Layout.flat (layout : Layout) (n : ℕ) : Fin (2*n) ↪ Cube (layout.log n) :=
  (wireIndex n).symm.toEmbedding.trans (layout.index n)

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

/-- Only output addresses need separation here; other fragments may read any
of these wires. Read separation of the hash is a property of its typing. -/
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

/-- Actual terms of every other component at the adapter's layers: its first
reduction at the input boundary, its later reductions, and its final product
layer, where other wires may be carried onward. -/
structure Others (layout : Layout) (leaves input final : ℕ) (output : Fin 2 ↪ Cube final) where
  first : Extension (F := F) (mid := input) (layout.flat (half leaves))
  pair : ∀ n, Extension (F := F) (mid := layout.log n) (layout.flat (half n))
  final : Extension (F := F) (mid := layout.log 2) output

def reduction (layout : Layout)
    (others : ∀ n, Extension (F := F) (mid := layout.log n) (layout.flat (half n))) {input : ℕ} :
    {n : ℕ} → Shape n → Layered.Circuit F (layout.log n) input → Layered.Circuit F (layout.log 2) input
  | _, .root, rest => rest
  | n, .pair next, rest => reduction layout others next
      (.layer (others n).checks
        (layer (pairRows n) (layout.index n) (layout.flat (half n)) (others n)) rest)

theorem reduction_eval (layout : Layout)
    (others : ∀ n, Extension (F := F) (mid := layout.log n) (layout.flat (half n))) {n input : ℕ}
    (shape : Shape n) (rest : Layered.Circuit F (layout.log n) input) (w : Cube input → F)
    (root : Wire 2) :
    (reduction layout others shape rest).eval w (layout.index 2 root) =
      roots shape (rest.eval w ∘ layout.index n) root := by
  induction shape with
  | root => rfl
  | @pair n next ih =>
      rw [reduction, ih, roots]
      apply congrArg (fun values => roots next values root)
      funext i
      change (layer (pairRows n) (layout.index n)
        (layout.flat (half n)) (others n)).outputs (rest.eval w)
          (layout.index (half n) i) = _
      have he : layout.index (half n) i =
          layout.flat (half n) (wireIndex (half n) i) := by simp [Layout.flat]
      rw [he, layer_outputs]
      symm
      exact stream_outputs (pairRows n) (rest.eval w ∘ layout.index n) _

variable {leaves input final : ℕ} (layout : Layout) (output : Fin 2 ↪ Cube final)

/-- Final product layer, later reductions, then the first reduction, which
reads the virtual leaves at `read` in the shared input array. -/
def body (shape : Shape (half leaves)) (others : Others (F := F) layout leaves input final output)
    (read : Wire leaves → Cube input) : Layered.Circuit F final input :=
  .layer others.final.checks (layer finalRows (layout.index 2) output others.final)
    (reduction layout others.pair shape (.layer others.first.checks
      (layer (pairRows leaves) read (layout.flat (half leaves)) others.first) .input))

def build {out : ℕ} (shape : Shape (half leaves)) (others : Others (F := F) layout leaves input final output)
    (carry : Cube out → Option (Cube final)) (read : Wire leaves → Cube input) :
    Layered.Circuit F out input :=
  .entry 2 ⟨carry,output⟩ (body layout output shape others read)

theorem body_eval (shape : Shape (half leaves)) (others : Others (F := F) layout leaves input final output)
    (read : Wire leaves → Cube input) (w : Cube input → F) (tree : Fin 2) :
    (body layout output shape others read).eval w (output tree) =
      ProductTree.eval (.pair shape) (w ∘ read) tree := by
  simp only [body, Layered.Circuit.eval, layer_outputs, ProductTree.eval, stream_outputs]
  congr 1
  funext root
  rw [Function.comp_apply, reduction_eval, roots]
  apply congrArg (fun values => roots shape values root)
  funext i
  change (layer (pairRows leaves) read (layout.flat (half leaves)) others.first).outputs w
    (layout.index (half leaves) i) = step (w ∘ read) i
  have he : layout.index (half leaves) i = layout.flat (half leaves) (wireIndex (half leaves) i) := by
    simp [Layout.flat]
  rw [he, layer_outputs]
  symm
  exact stream_outputs (pairRows leaves) (w ∘ read) _

theorem build_satisfies {out : ℕ} (shape : Shape (half leaves))
    (others : Others (F := F) layout leaves input final output) (carry : Cube out → Option (Cube final))
    (read : Wire leaves → Cube input) (w : Cube input → F)
    (h : (build layout output shape others carry read).Satisfies w) :
    ProductTree.Satisfies (.pair shape) (w ∘ read) := by
  intro tree
  have hz := h.1 tree
  change (body layout output shape others read).eval w (output tree) = 0 at hz
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
adapter checks: satisfaction of the complete joint circuit gives a unit
product of the virtual leaves in each tree. -/
theorem full_products {out upper : ℕ} [CharP F 2] (shape : Shape (half leaves))
    (others : Others (F := F) layout leaves input final output)
    (carry : Cube out → Option (Cube final)) (above : Above F upper out)
    (read : Wire leaves → Cube input) (w : Cube input → F)
    (h : (above.plug (build layout output shape others carry read)).Satisfies w) :
    ∀ tree, ∏ i, w (read (tree,i)) = 1 :=
  (ProductTree.satisfies_iff _ _).mp
    (build_satisfies layout output shape others carry read w (above.satisfies _ _ h))

end LfzkV2.Current.Adapter.Fragment
