import LfzkV2.Current.ApplicationSetup
import LfzkV2.Current.CanonicalPrefix
import LfzkV2.Current.SegmentedCircuit

/-! Identifier inputs used by the current runtime. Hashing is an explicit
auxiliary function; the bytes it receives are fixed here, rather than supplied
by a proof-dependent metadata callback. In particular the identifier of the
archived adapter fragment uses the same sparse rows as its algebraic model.

The LFC3 hash input authenticates the stored coefficient table, delta
dictionaries, segment indices and tokens. Compression changes the identity.
This is `core/proto/src/v2/encoding.rs`; expansion supplies the algebraic
circuit, while the fixed fragment (`foreign::adapter::fragment`) has
single-run streams and the one coefficient `1`. -/
noncomputable section
namespace LfzkV2.Current.MetadataIdentifiers
open SumcheckV2 Layered Adapter.Circuit Adapter.ProductTree
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

/-- One reduction layer of `n` wires per tree, reading `2*n` wires of an
array of width `inputs` from offset `base`: `g = t*half n+i`,
`l = base+t*n+2*i`, exactly as the runtime builder emits them. -/
def pairLayer (base n inputs : ℕ) : Layer F :=
  ⟨inputs,(stream (pairRows (F := F) n)).map
    (Term.map Fin.val (fun wire => base+(wireIndex n wire).val))⟩

/-- The runtime builds from the inputs upwards and reverses once at the end.
The recursion below therefore emits the rootward reductions first. -/
def reductions : {n : ℕ} → Shape n → List (Layer F)
  | _, .root => []
  | n, .pair rest => reductions rest ++ [pairLayer 0 n (2*n)]

/-- Preserve each stream's order and use Rust's first-occurrence delta
interning. The coefficient index is supplied by the circuit's table builder. -/
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

/-- The final product layer: output `t` is `l*r + 1` on wires `2t, 2t+1`. -/
def finalLayer : Layer F :=
  ⟨4,(stream (finalRows (F := F))).map (Term.map Fin.val (fun wire => (wireIndex 2 wire).val))⟩

/-- LFC3 identity bytes of the archived adapter fragment. Its first
reduction reads the virtual leaves from `virtualStart` of the shared input
array of width `inputs`; every coefficient is table entry zero, the one. -/
def fragmentBytes (encode : F → Bytes) {leaves : ℕ} (shape : Shape (half leaves))
    (inputs publicInputs virtualStart : ℕ) : Bytes :=
  circuitBytes 4 true 16 encode 2 1 inputs publicInputs [1]
    ((finalLayer (F := F) :: reductions (F := F) shape ++ [pairLayer virtualStart leaves inputs]).map
      fun layer => storedLayer layer fun _ _ => 0)

/-- Only this final hash operation remains abstract. It may be instantiated
with SHA-256, as in Rust, or with the identifier oracle in the proof model. -/
def fragmentId (hash : Bytes → Digest) (encode : F → Bytes) {leaves : ℕ} (shape : Shape (half leaves))
    (inputs publicInputs virtualStart : ℕ) : Digest :=
  hash (fragmentBytes encode shape inputs publicInputs virtualStart)

end LfzkV2.Current.MetadataIdentifiers
