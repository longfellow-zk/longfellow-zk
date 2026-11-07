import LfzkV2.Current.ConcreteTopology
import LfzkV2.Current.FrontendTopology

/-! Sparse trusted hash topology around the generated cross-field adapter.
The generated component is second in the supplied circuit list. Its sparse
fragment therefore follows the hash fragment at every shared layer. The
adapter contributes no internal assertion markers: its two zero outputs
enter together at its first layer. This constructor supports a hash component
strictly deeper than the adapter, as in the current mdoc setup.
The concrete endpoint checks that depth restriction in its public bounds. -/
noncomputable section
namespace LfzkV2.Current.ConcreteAdapterTopology
open SumcheckV2 ConcreteTopology
open scoped Classical
variable {F : Type} [Field F]

structure Extension {n out mid : ℕ} (output : Fin n ↪ Cube out) (F : Type) where
  fragments : List (ConcreteTopology.Fragment out mid F)
  disjoint : ∀ term ∈ Layered.flatten (fragments.map ConcreteTopology.Fragment.quads),
    ∀ g, term.output ≠ output g

namespace Extension
variable {n out mid : ℕ} {output : Fin n ↪ Cube out} (extension : Extension (mid := mid) output F)

def withComponent (component : ℕ) : Extension (mid := mid) output F where
  fragments := extension.fragments.map (ConcreteTopology.Fragment.withComponent component)
  disjoint := by
    simpa only [List.map_map,Function.comp_def,ConcreteTopology.Fragment.withComponent] using extension.disjoint

def algebraic : Adapter.Circuit.Fragment.Extension (F := F) (mid := mid) output where
  terms := Layered.flatten (extension.fragments.map ConcreteTopology.Fragment.quads)
  disjoint := extension.disjoint
  checks := Layer.checks extension.fragments
  assertions := Layer.assertions extension.fragments

def metadata {W : Type} (rows : Fin n → Adapter.Circuit.Row W F)
    (input : W → Cube mid) (localLayer : ℕ) :
    FrontendSchedule.LayerMetadata (Adapter.Circuit.Fragment.layer rows input output extension.algebraic) where
  fragments := extension.fragments.map ConcreteTopology.Fragment.metadata ++ [⟨1,localLayer,0,0⟩]
  count := by
    simpa only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,Layer.metadata,algebraic] using (Layer.metadata extension.fragments).count
  quadratic_first := by
    intro i
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,algebraic,Adapter.Circuit.Fragment.layer,Layered.sparseLayer]
    rw [← Layer.quadratic_length]
    unfold Layer.assertions
    split <;> simp_all [FrontendSchedule.isQuadratic]

end Extension

structure Others (layout : Adapter.Circuit.Layout) (d q input final : ℕ)
    (output : Fin 2 ↪ Cube final) (F : Type) where
  leaf : Extension (mid := input) (layout.flat d q) F
  pair : ∀ d q, Extension (mid := layout.log d q) (layout.flat (Adapter.Circuit.half d) (Adapter.Circuit.half q)) F
  final : Extension (mid := layout.log 1 1) output F

namespace Others
variable {layout : Adapter.Circuit.Layout} {d q input final : ℕ}
  {output : Fin 2 ↪ Cube final} (others : Others layout d q input final output F)

def withComponent (component : ℕ) : Others layout d q input final output F where
  leaf := others.leaf.withComponent component
  pair d q := (others.pair d q).withComponent component
  final := others.final.withComponent component

def algebraic : Adapter.Circuit.Fragment.Others (F := F) layout d q input final output where
  leaf := others.leaf.algebraic
  pair d q := (others.pair d q).algebraic
  final := others.final.algebraic

end Others

def depth {d q : ℕ} : Adapter.Circuit.Shape d q → ℕ
  | .root => 0
  | .pair next => 1+depth next

def reductionPlan {layout : Adapter.Circuit.Layout} {d q input : ℕ}
    (others : ∀ d q, Extension (mid := layout.log d q)
      (layout.flat (Adapter.Circuit.half d) (Adapter.Circuit.half q)) F)
    (shape : Adapter.Circuit.Shape d q) (rest : Layered.Circuit F (layout.log d q) input)
    (plan : FrontendSchedule.Plan F rest) :
    FrontendSchedule.Plan F (Adapter.Circuit.Fragment.reduction layout
      (fun d q => (others d q).algebraic) shape rest) := by
  induction shape with
  | root => exact plan
  | @pair d q next ih =>
      exact ih _ (.layer ((others d q).metadata (Adapter.Circuit.pairRows d q)
        (layout.index d q) (depth next+1)) plan)

def buildPlan {layout : Adapter.Circuit.Layout} {d q input final out : ℕ}
    (shape : Adapter.Circuit.Shape d q) {output : Fin 2 ↪ Cube final}
    (others : Others layout d q input final output F)
    (carry : Cube out → Option (Cube final))
    (sources : Fin d → Cube input) (pads : Fin 2 → Fin q → Cube input)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) :
    FrontendSchedule.Plan F (Adapter.Circuit.Fragment.build layout output shape others.algebraic
      carry sources pads powers base masked targets) :=
  .entryLayer ⟨[⟨1,2⟩],rfl⟩ ⟨carry,output⟩
    (others.final.metadata (Adapter.Circuit.finalRows targets) (layout.index 1 1) 0)
    (reductionPlan others.pair shape _
      (.layer (others.leaf.metadata (Adapter.Circuit.leafRows sources pads powers base masked)
        id (depth shape+1)) .input))

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

def algebraic : {out base : ℕ} → Above F out base → Adapter.Circuit.Fragment.Above F out base
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
