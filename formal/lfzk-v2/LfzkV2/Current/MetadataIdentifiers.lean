import LfzkV2.Current.ApplicationSetup
import LfzkV2.Current.CanonicalPrefix
import LfzkV2.Current.SegmentedCircuit

/-! Identifier inputs used by the current runtime. Hashing is an explicit
auxiliary function; the bytes it receives are fixed here, rather than supplied
by a proof-dependent metadata callback. In particular the adapter identifier
uses the same generated sparse rows as its algebraic circuit model.

The LFC3 hash input authenticates the stored coefficient table, delta
dictionaries, segment indices and tokens. Compression changes the identity.
This is `core/proto/src/v2/encoding.rs`; expansion supplies the algebraic
circuit, while the generated adapter template fixes its own single-run streams. -/
noncomputable section
namespace LfzkV2.Current.MetadataIdentifiers
open SumcheckV2 Layered Adapter.Circuit
open TranscriptV2.Framing (encodeLE)

variable {F : Type} [Field F]

structure Layer (F : Type) where
  inputs : ℕ
  terms : List (Layered.Term ℕ ℕ F)

/-- The raw identity header uses unframed little-endian words, unlike the
transcript's `write_bytes` operation. It starts with the runtime `FieldID`
(`Gf2_128 = 4`, `P256 = 1`), which distinguishes fields whose encodings of
`-1` coincide. Coefficients precede the stored layers. -/
def circuitBytes (fieldId : ℕ) (binary : Bool) (width : ℕ) (encode : F → Bytes)
    (outputs logOutput inputs publicInputs : ℕ) (constants : List F)
    (layers : List SegmentedCircuit.Layer) : Bytes :=
  CanonicalPrefix.utf8 "LFC3-v2-segmented-id-v3" ++ encodeLE 8 fieldId ++
    encodeLE 8 (if binary then 1 else 0) ++ encodeLE 8 width ++ encode (-1) ++
    [outputs,logOutput,inputs,publicInputs,layers.length,constants.length].flatMap (encodeLE 8) ++
    constants.flatMap encode ++ layers.flatMap SegmentedCircuit.layerBytes

def pairLayer (d q : ℕ) : Layer F :=
  ⟨2*(d+q),(stream (pairRows (F := F) d q)).map
    (Term.map Fin.val (fun wire => (wireIndex d q wire).val))⟩

/-- The runtime builds from leaves upwards and reverses once at the end.
The recursion below therefore emits the rootward reductions first. -/
def reductions : {d q : ℕ} → Shape d q → List (Layer F)
  | _, _, .root => []
  | d, q, .pair rest => reductions rest ++ [pairLayer d q]

/-- Preserve each stream's order and use Rust's first-occurrence delta
interning. The coefficient index is supplied by the template's table builder. -/
def storedLayer (layer : Layer F)
    (coefficient : ℕ → Layered.Term ℕ ℕ F → ℕ) : SegmentedCircuit.Layer :=
  let indexed := layer.terms.zipIdx
  { inputs := layer.inputs
    logInputs := Nat.clog 2 layer.inputs
    quadratic := SegmentedCircuit.fromTerms (indexed.filterMap fun (term,i) =>
      match term with
      | .quadratic g l r _ => some ![SegmentedCircuit.word g,SegmentedCircuit.word l,
          SegmentedCircuit.word r,SegmentedCircuit.word (coefficient i term)]
      | _ => none)
    linear := SegmentedCircuit.fromTerms (indexed.filterMap fun (term,i) =>
      match term with
      | .linear g l _ => some ![SegmentedCircuit.word g,SegmentedCircuit.word l,
          SegmentedCircuit.word (coefficient i term)]
      | _ => none)
    constant := SegmentedCircuit.fromTerms (indexed.filterMap fun (term,i) =>
      match term with
      | .constant g _ => some ![SegmentedCircuit.word g,SegmentedCircuit.word (coefficient i term)]
      | _ => none) }

/-- Every leaf appends its power and base, including duplicate values. Its
second linear coefficient refers to the initial table entry, one. -/
def leafConstants (leaf : Layer F) : List F :=
  leaf.terms.zipIdx.filterMap fun (term,i) =>
    if i % 3 = 1 then none else
      match term with
      | .linear _ _ k | .constant _ k => some k
      | _ => none

private def leafCoefficient (i : ℕ) (term : Layered.Term ℕ ℕ F) : ℕ :=
  match term with
  | .linear g _ _ => if i % 3 = 0 then 2*g+1 else 0
  | .constant g _ => 2*g+2
  | _ => 0

def adapterBytes {d q : ℕ} (encode : F → Bytes) (shape : Shape d q)
    (inputs publicInputs : ℕ) (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) : Bytes :=
  let leaf : Layer F := ⟨inputs,(stream (leafRows sources pads powers base masked)).map (Term.map Fin.val id)⟩
  let coefficients := leafConstants leaf
  let constants := [1] ++ coefficients ++ (List.ofFn fun tree => (targets tree : F))
  let finalLayer : Layer F := ⟨4,(stream (finalRows targets)).map
    (Term.map Fin.val (fun wire => (wireIndex 1 1 wire).val))⟩
  let finalStored := storedLayer finalLayer fun _ term =>
    match term with
    | .constant g _ => 1+coefficients.length+g
    | _ => 0
  circuitBytes 4 true 16 encode 2 1 inputs publicInputs constants
    (finalStored :: (reductions (F := F) shape).map (fun layer => storedLayer layer (fun _ _ => 0)) ++
      [storedLayer leaf (leafCoefficient (F := F))])

/-- Only this final hash operation remains abstract. It may be instantiated
with SHA-256, as in Rust, or with the identifier oracle in the proof model. -/
def adapterId {d q : ℕ} (hash : Bytes → Digest) (encode : F → Bytes) (shape : Shape d q)
    (inputs publicInputs : ℕ) (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) : Digest :=
  hash (adapterBytes encode shape inputs publicInputs sources pads powers base masked targets)

end LfzkV2.Current.MetadataIdentifiers
