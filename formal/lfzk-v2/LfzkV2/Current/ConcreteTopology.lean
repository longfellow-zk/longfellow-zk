import LfzkV2.Current.FrontendSchedule
import LfzkV2.Layered.SparseLayer

/-! Trusted sparse topology constructs both algebraic layers and transcript
annotations. Assertion counts and classes cannot be supplied independently
of the gates that the verifier checks. Component identifiers and sparse
coordinate maps are ordinary trusted circuit data. -/
noncomputable section
namespace LfzkV2.Current.ConcreteTopology
open SumcheckV2
open scoped Classical

variable {F : Type} [Field F]

/-- A fragment owns sparse gates and local assertion markers, never a wire
array. Its coordinate maps refer to the one global array at this layer. -/
structure Fragment (out mid : ℕ) (F : Type) where
  circuit : ℕ
  layer : ℕ
  quads : Layered.QuadFragment (Cube out) (Cube mid) F
  quadratic : List (Fin quads.inputs × Fin quads.inputs)
  linear : List (Fin quads.inputs)

namespace Fragment

def withComponent {out mid : ℕ} (component : ℕ) (fragment : Fragment out mid F) : Fragment out mid F :=
  { fragment with circuit := component }

def metadata {out mid : ℕ} (fragment : Fragment out mid F) : Current.Fragment :=
  ⟨fragment.circuit,fragment.layer,fragment.quadratic.length,fragment.linear.length⟩

def quadraticWires {out mid : ℕ} (fragment : Fragment out mid F) :
    List (Cube mid × Cube mid) :=
  fragment.quadratic.map fun pair => (fragment.quads.inputIndex pair.1,fragment.quads.inputIndex pair.2)

def linearWires {out mid : ℕ} (fragment : Fragment out mid F) : List (Cube mid) :=
  fragment.linear.map fragment.quads.inputIndex

end Fragment

namespace Layer
variable {out mid : ℕ} (fragments : List (Fragment out mid F))

def quadratic := fragments.flatMap Fragment.quadraticWires
def linear := fragments.flatMap Fragment.linearWires
def checks := (quadratic fragments).length+(linear fragments).length

def assertions (index : Fin (checks fragments)) : LfzkV2.Native.AssertionTerm (Cube mid) :=
  if h : index.val < (quadratic fragments).length then
    let pair := (quadratic fragments).get ⟨index.val,h⟩
    .quadratic pair.1 pair.2
  else .linear ((linear fragments).get ⟨index.val-(quadratic fragments).length,by
    have hi := index.isLt
    dsimp [checks] at hi
    omega⟩)

def circuit : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin (checks fragments)) F :=
  Layered.sparseLayer (Layered.flatten (fragments.map Fragment.quads)) (assertions fragments)

omit [Field F] in
theorem quadratic_length : (quadratic fragments).length =
    ((fragments.map Fragment.metadata).map Current.Fragment.quadraticAssertions).sum := by
  simp [quadratic,Fragment.quadraticWires,Fragment.metadata,List.map_map,Function.comp_def]

omit [Field F] in
theorem linear_length : (linear fragments).length =
    ((fragments.map Fragment.metadata).map Current.Fragment.linearAssertions).sum := by
  simp [linear,Fragment.linearWires,Fragment.metadata,List.map_map,Function.comp_def]

/-- Assertion weights visit all quadratic markers in fragment order,
then all linear markers in the same order, matching the runtime. -/
def metadata : FrontendSchedule.LayerMetadata (circuit fragments) where
  fragments := fragments.map Fragment.metadata
  count := by rw [← quadratic_length,← linear_length]; rfl
  quadratic_first := by
    intro i
    change FrontendSchedule.isQuadratic (assertions fragments i) = _
    rw [← quadratic_length]
    unfold assertions
    split <;> simp_all [FrontendSchedule.isQuadratic]

end Layer

/-- Zero outputs are stored at their actual layer. Their annotations and
their coefficient count come from this same list of output addresses. -/
structure EntryBlock (wire : Type) where
  circuit : ℕ
  outputs : List wire

namespace EntryBlock

def withComponent {wire : Type} (component : ℕ) (entry : EntryBlock wire) : EntryBlock wire :=
  { entry with circuit := component }

def metadata {wire : Type} (entry : EntryBlock wire) : Current.Entry :=
  ⟨entry.circuit,entry.outputs.length⟩

end EntryBlock

structure EntryLayout (out next : ℕ) where
  carry : Cube out → Option (Cube next)
  blocks : List (EntryBlock (Cube next))

namespace EntryLayout
variable {out next : ℕ} (entry : EntryLayout out next)

def withComponent (component : ℕ) : EntryLayout out next :=
  { entry with blocks := entry.blocks.map (EntryBlock.withComponent component) }

def outputs : List (Cube next) := entry.blocks.flatMap EntryBlock.outputs
def circuit : Layered.Entry (Cube out) (Cube next) entry.outputs.length :=
  ⟨entry.carry,entry.outputs.get⟩

def metadata : FrontendSchedule.EntryMetadata entry.outputs.length where
  entries := entry.blocks.map EntryBlock.metadata
  count := by simp [outputs,EntryBlock.metadata,List.map_map,Function.comp_def]

end EntryLayout

/-- This is the normalized runtime grammar. Entries add output checks at
an existing boundary; a layer adds exactly one shared sumcheck regardless
of its number of sparse fragments. -/
inductive Circuit (F : Type) : ℕ → ℕ → Type where
  | input {n : ℕ} : Circuit F n n
  | inputEntry {out input : ℕ} (entry : EntryLayout out input) : Circuit F out input
  | layer {out mid input : ℕ} (fragments : List (Fragment out mid F))
      (rest : Circuit F mid input) : Circuit F out input
  | entryLayer {out next mid input : ℕ} (entry : EntryLayout out next)
      (fragments : List (Fragment next mid F)) (rest : Circuit F mid input) : Circuit F out input

namespace Circuit

/-- Component indices are assigned by the runtime's supplied circuit list.
They do not come from the archived gate description. -/
def withComponent (component : ℕ) : {out input : ℕ} → Circuit F out input → Circuit F out input
  | _, _, .input => .input
  | _, _, .inputEntry entry => .inputEntry (entry.withComponent component)
  | _, _, .layer fragments rest => .layer
      (fragments.map (Fragment.withComponent component)) (rest.withComponent component)
  | _, _, .entryLayer entry fragments rest => .entryLayer (entry.withComponent component)
      (fragments.map (Fragment.withComponent component)) (rest.withComponent component)

def algebraic : {out input : ℕ} → Circuit F out input → Layered.Circuit F out input
  | _, _, .input => .input
  | _, _, .inputEntry entry => .entry entry.outputs.length entry.circuit .input
  | _, _, .layer fragments rest => .layer (Layer.checks fragments) (Layer.circuit fragments) rest.algebraic
  | _, _, .entryLayer entry fragments rest => .entry entry.outputs.length entry.circuit
      (.layer (Layer.checks fragments) (Layer.circuit fragments) rest.algebraic)

def plan : {out input : ℕ} → (circuit : Circuit F out input) → FrontendSchedule.Plan F circuit.algebraic
  | _, _, .input => .input
  | _, _, .inputEntry entry => .inputEntry entry.metadata entry.circuit
  | _, _, .layer fragments rest => .layer (Layer.metadata fragments) rest.plan
  | _, _, .entryLayer entry fragments rest =>
      .entryLayer entry.metadata entry.circuit (Layer.metadata fragments) rest.plan

end Circuit
end LfzkV2.Current.ConcreteTopology
