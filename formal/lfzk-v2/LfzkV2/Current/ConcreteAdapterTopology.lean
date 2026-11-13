import LfzkV2.Current.ConcreteTopology
import LfzkV2.Current.AdapterFragment

/-! Sparse trusted hash topology around the fixed adapter fragment. The hash
is component zero and the archived adapter fragment component one. At every
shared layer the hash fragments precede the adapter's, as in the runtime
schedule, which orders components by decreasing depth. The adapter's two zero
outputs enter together at its first layer.

Read separation is a consequence of the types, not a certificate. A hash
fragment at a shared layer has typed coordinates: at the input boundary it
reads only its own input prefix `Fin width`, which ends before R, the quotient
pads and the virtual leaves; at later shared layers it reads and writes only
wires outside the adapter's arrays. Its carried outputs avoid the adapter's
outputs by type as well. -/
noncomputable section
namespace LfzkV2.Current.ConcreteAdapterTopology
open SumcheckV2 ConcreteTopology Adapter.Circuit Adapter.ProductTree
open scoped Classical
variable {F : Type} [Field F]

/-- Positions of a cube that an embedded array does not occupy. -/
abbrev Avoid {k m : ℕ} (e : Fin k ↪ Cube m) := {u : Cube m // ∀ i, e i ≠ u}

/-- One hash fragment at a layer shared with the adapter. Its sparse terms
use local indices, mapped to typed output and input coordinates. -/
structure Local (O W F : Type) where
  circuit : ℕ
  layer : ℕ
  quads : Layered.QuadFragment O W F
  quadratic : List (Fin quads.inputs × Fin quads.inputs)
  linear : List (Fin quads.inputs)

namespace Local
variable {O W : Type}

def withComponent (component : ℕ) (fragment : Local O W F) : Local O W F :=
  { fragment with circuit := component }

/-- Place typed coordinates in the dense global arrays of the layer. -/
def place {out mid : ℕ} (fragment : Local O W F) (outputs : O → Cube out) (inputs : W → Cube mid) :
    ConcreteTopology.Fragment out mid F where
  circuit := fragment.circuit
  layer := fragment.layer
  quads := ⟨fragment.quads.outputs,fragment.quads.inputs,outputs ∘ fragment.quads.outputIndex,
    inputs ∘ fragment.quads.inputIndex,fragment.quads.terms⟩
  quadratic := fragment.quadratic
  linear := fragment.linear

end Local

/-- Every wire a term reads lies in the range of `read`. -/
def TermReads {O W W' : Type} (read : W → W') : Layered.Term O W' F → Prop
  | .quadratic _ l r _ => (∃ x, read x = l) ∧ ∃ x, read x = r
  | .linear _ l _ => ∃ x, read x = l
  | .constant _ _ => True

def AssertionReads {W W' : Type} (read : W → W') : LfzkV2.Native.AssertionTerm W' → Prop
  | .quadratic l r => (∃ x, read x = l) ∧ ∃ x, read x = r
  | .linear l => ∃ x, read x = l

/-- Hash fragments at one shared layer: outputs avoid the adapter's outputs,
and inputs are typed by `W`, placed by `read`. -/
structure Extension {n out mid : ℕ} (output : Fin n ↪ Cube out) (W : Type) (read : W → Cube mid)
    (F : Type) where
  fragments : List (Local (Avoid output) W F)

namespace Extension
variable {n out mid : ℕ} {output : Fin n ↪ Cube out} {W : Type} {read : W → Cube mid}
variable (extension : Extension output W read F)

def global : List (ConcreteTopology.Fragment out mid F) :=
  extension.fragments.map fun fragment => fragment.place Subtype.val read

def withComponent (component : ℕ) : Extension output W read F :=
  ⟨extension.fragments.map (Local.withComponent component)⟩

omit [Field F] in
private theorem mem_terms (term : Layered.Term (Cube out) (Cube mid) F)
    (h : term ∈ Layered.flatten (extension.global.map ConcreteTopology.Fragment.quads)) :
    ∃ fragment ∈ extension.fragments, ∃ t ∈ fragment.quads.terms,
      term = t.map (Subtype.val ∘ fragment.quads.outputIndex) (read ∘ fragment.quads.inputIndex) := by
  unfold Layered.flatten global at h
  rw [List.map_map,List.mem_flatMap] at h
  obtain ⟨quads,hq,ht⟩ := h
  obtain ⟨fragment,hf,rfl⟩ := List.mem_map.mp hq
  obtain ⟨t,htm,rfl⟩ := List.mem_map.mp ht
  exact ⟨fragment,hf,t,htm,rfl⟩

omit [Field F] in
/-- Output disjointness holds by the output type. -/
theorem disjoint : ∀ term ∈ Layered.flatten (extension.global.map ConcreteTopology.Fragment.quads),
    ∀ g, term.output ≠ output g := by
  intro term h g
  obtain ⟨fragment,_,t,_,rfl⟩ := extension.mem_terms term h
  cases t <;>
    exact fun e => ((fragment.quads.outputIndex _).property g) e.symm

omit [Field F] in
/-- Every sparse read goes through the typed input map. -/
theorem reads : ∀ term ∈ Layered.flatten (extension.global.map ConcreteTopology.Fragment.quads),
    TermReads read term := by
  intro term h
  obtain ⟨fragment,_,t,_,rfl⟩ := extension.mem_terms term h
  cases t <;> simp [TermReads,Layered.Term.map]

omit [Field F] in
/-- Every assertion marker reads through the typed input map. -/
theorem assertion_reads (i : Fin (Layer.checks extension.global)) :
    AssertionReads read (Layer.assertions extension.global i) := by
  unfold Layer.assertions
  split
  · rename_i h
    obtain ⟨pair,hp⟩ : ∃ pair, (Layer.quadratic extension.global).get ⟨i.val,h⟩ = pair := ⟨_,rfl⟩
    have hm := List.get_mem (Layer.quadratic extension.global) ⟨i.val,h⟩
    rw [hp] at hm ⊢
    simp only [Layer.quadratic,global,List.mem_flatMap,List.mem_map,Fragment.quadraticWires,
      Local.place] at hm
    obtain ⟨_,⟨fragment,_,rfl⟩,q,_,rfl⟩ := hm
    exact ⟨⟨_,rfl⟩,⟨_,rfl⟩⟩
  · rename_i h
    have hm := List.get_mem (Layer.linear extension.global)
      ⟨i.val-(Layer.quadratic extension.global).length,by
        have hi := i.isLt
        dsimp [Layer.checks] at hi
        omega⟩
    generalize (Layer.linear extension.global).get _ = wire at hm ⊢
    simp only [Layer.linear,global,List.mem_flatMap,List.mem_map,Fragment.linearWires,
      Local.place] at hm
    obtain ⟨_,⟨fragment,_,rfl⟩,q,_,rfl⟩ := hm
    exact ⟨_,rfl⟩

def algebraic : Adapter.Fragment.Extension (F := F) (mid := mid) output where
  terms := Layered.flatten (extension.global.map ConcreteTopology.Fragment.quads)
  disjoint := extension.disjoint
  checks := Layer.checks extension.global
  assertions := Layer.assertions extension.global

/-- The hash fragments' metadata, then the adapter's one fragment, which
has no assertion markers of its own. -/
def metadata {V : Type} (rows : Fin n → Row V F) (input : V → Cube mid) (localLayer : ℕ) :
    FrontendSchedule.LayerMetadata (Adapter.Fragment.layer rows input output extension.algebraic) where
  fragments := extension.global.map ConcreteTopology.Fragment.metadata ++ [⟨1,localLayer,0,0⟩]
  count := by
    simpa only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,Layer.metadata,algebraic] using (Layer.metadata extension.global).count
  quadratic_first := by
    intro i
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,algebraic,Adapter.Fragment.layer,Layered.sparseLayer]
    rw [← Layer.quadratic_length]
    unfold Layer.assertions
    split <;> simp_all [FrontendSchedule.isQuadratic]

end Extension

/-- Hash fragments at every adapter layer. The input-boundary fragments read
the hash's own prefix of `width` inputs, placed by `place`; later fragments
read only wires outside the adapter's arrays. -/
structure Others (layout : Adapter.Fragment.Layout) (leaves width input final : ℕ)
    (place : Fin width → Cube input) (output : Fin 2 ↪ Cube final) (F : Type) where
  first : Extension (layout.flat (half leaves)) (Fin width) place F
  pair : ∀ n, Extension (layout.flat (half n)) (Avoid (layout.flat n)) Subtype.val F
  final : Extension output (Avoid (layout.flat 2)) Subtype.val F

namespace Others
variable {layout : Adapter.Fragment.Layout} {leaves width input final : ℕ}
  {place : Fin width → Cube input} {output : Fin 2 ↪ Cube final}
  (others : Others layout leaves width input final place output F)

def withComponent (component : ℕ) : Others layout leaves width input final place output F where
  first := others.first.withComponent component
  pair n := (others.pair n).withComponent component
  final := others.final.withComponent component

def algebraic : Adapter.Fragment.Others (F := F) layout leaves input final output where
  first := others.first.algebraic
  pair n := (others.pair n).algebraic
  final := others.final.algebraic

end Others

/-- Carried wires of the final shared layer; they avoid the adapter outputs. -/
def carryWires {out final : ℕ} {output : Fin 2 ↪ Cube final}
    (carry : Cube out → Option (Avoid output)) : Cube out → Option (Cube final) :=
  fun u => (carry u).map Subtype.val

def reductionPlan {layout : Adapter.Fragment.Layout} {input : ℕ}
    (others : ∀ n, Extension (layout.flat (half n)) (Avoid (layout.flat n)) Subtype.val F) :
    {n : ℕ} → (shape : Shape n) → (rest : Layered.Circuit F (layout.log n) input) →
    FrontendSchedule.Plan F rest →
    FrontendSchedule.Plan F (Adapter.Fragment.reduction layout (fun n => (others n).algebraic) shape rest)
  | _, .root, _, plan => plan
  | n, .pair next, _, plan => reductionPlan others next _
      (.layer ((others n).metadata (pairRows n) (layout.index n) (depth next+1)) plan)

/-- The adapter's local layer indices count from its output layer, as the
runtime's reversed layer list does: final 0, then each reduction. -/
def buildPlan {layout : Adapter.Fragment.Layout} {leaves width input final out : ℕ}
    {place : Fin width → Cube input} {output : Fin 2 ↪ Cube final}
    (shape : Shape (half leaves)) (others : Others layout leaves width input final place output F)
    (carry : Cube out → Option (Avoid output)) (read : Wire leaves → Cube input) :
    FrontendSchedule.Plan F (Adapter.Fragment.build layout output shape others.algebraic
      (carryWires carry) read) :=
  .entryLayer ⟨[⟨1,2⟩],rfl⟩ ⟨carryWires carry,output⟩
    (others.final.metadata finalRows (layout.index 2) 0)
    (reductionPlan others.pair shape _
      (.layer (others.first.metadata (pairRows leaves) read (depth shape+1)) .input))

/-- Only complete layers occur above the generated component's output
entry. Keeping this grammar prevents adjacent entry blocks from silently
creating another transcript boundary. -/
inductive Above (F : Type) : ℕ → ℕ → Type where
  | hole {n : ℕ} : Above F n n
  | layer {out mid base : ℕ} (fragments : List (ConcreteTopology.Fragment out mid F))
      (rest : Above F mid base) : Above F out base
  | entryLayer {out next mid base : ℕ} (entry : EntryLayout out next)
      (fragments : List (ConcreteTopology.Fragment next mid F)) (rest : Above F mid base) : Above F out base

namespace Above

def withComponent (component : ℕ) : {out base : ℕ} → Above F out base → Above F out base
  | _, _, .hole => .hole
  | _, _, .layer fragments rest => .layer
      (fragments.map (ConcreteTopology.Fragment.withComponent component)) (rest.withComponent component)
  | _, _, .entryLayer entry fragments rest => .entryLayer (entry.withComponent component)
      (fragments.map (ConcreteTopology.Fragment.withComponent component)) (rest.withComponent component)

def algebraic : {out base : ℕ} → Above F out base → Adapter.Fragment.Above F out base
  | _, _, .hole => .hole
  | _, _, .layer fragments rest => .layer (Layer.checks fragments) (Layer.circuit fragments) rest.algebraic
  | _, _, .entryLayer entry fragments rest => .entry entry.outputs.length entry.circuit
      (.layer (Layer.checks fragments) (Layer.circuit fragments) rest.algebraic)

def plan {out base input : ℕ} (above : Above F out base) (rest : Layered.Circuit F base input)
    (tail : FrontendSchedule.Plan F rest) : FrontendSchedule.Plan F (above.algebraic.plug rest) := by
  induction above with
  | hole => exact tail
  | layer fragments _ ih => exact .layer (Layer.metadata fragments) (ih rest tail)
  | entryLayer entry fragments _ ih =>
      exact .entryLayer entry.metadata entry.circuit (Layer.metadata fragments) (ih rest tail)

end Above
end LfzkV2.Current.ConcreteAdapterTopology
