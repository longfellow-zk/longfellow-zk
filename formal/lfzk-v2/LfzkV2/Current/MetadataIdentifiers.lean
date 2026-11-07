import LfzkV2.Current.ApplicationSetup
import LfzkV2.Current.CanonicalPrefix

/-! Identifier inputs used by the current runtime. Hashing is an explicit
auxiliary function; the bytes it receives are fixed here, rather than supplied
by a proof-dependent metadata callback. In particular the adapter identifier
uses the same generated sparse rows as its algebraic circuit model.

The LFC3 hash input is independent of stream compression. Each of the three
streams retains its own term order, and coefficients are serialized by value.
This is `core/proto/src/v2/encoding.rs`, not an encoding of the combined
sumcheck tensor. -/
noncomputable section
namespace LfzkV2.Current.MetadataIdentifiers
open SumcheckV2 Layered Adapter.Circuit
open TranscriptV2.Framing (encodeLE)

variable {F : Type} [Field F]

structure Layer (F : Type) where
  inputs : ℕ
  terms : List (Layered.Term ℕ ℕ F)

def quadratic (encode : F → Bytes) : Layered.Term ℕ ℕ F → Option Bytes
  | .quadratic g l r k => some (encodeLE 8 g ++ encodeLE 8 l ++ encodeLE 8 r ++ encode k)
  | _ => none

def linear (encode : F → Bytes) : Layered.Term ℕ ℕ F → Option Bytes
  | .linear g l k => some (encodeLE 8 g ++ encodeLE 8 l ++ encode k)
  | _ => none

def constant (encode : F → Bytes) : Layered.Term ℕ ℕ F → Option Bytes
  | .constant g k => some (encodeLE 8 g ++ encode k)
  | _ => none

/-- A stream tag and term count precede the concatenated records. -/
def streamBytes (tag : ℕ) (terms : List Bytes) : Bytes :=
  encodeLE 8 tag ++ encodeLE 8 terms.length ++ terms.flatten

def layerBytes (encode : F → Bytes) (layer : Layer F) : Bytes :=
  encodeLE 8 layer.inputs ++ encodeLE 8 (Nat.clog 2 layer.inputs) ++
    streamBytes 0 (layer.terms.filterMap (quadratic encode)) ++
    streamBytes 1 (layer.terms.filterMap (linear encode)) ++
    streamBytes 2 (layer.terms.filterMap (constant encode))

/-- The raw identity header uses unframed little-endian words, unlike the
transcript's `write_bytes` operation. -/
def circuitBytes (binary : Bool) (width : ℕ) (encode : F → Bytes)
    (outputs logOutput inputs publicInputs : ℕ) (layers : List (Layer F)) : Bytes :=
  CanonicalPrefix.utf8 "LFC3-v2-three-streams-v2" ++
    encodeLE 8 (if binary then 1 else 0) ++ encodeLE 8 width ++ encode (-1) ++
    [outputs,logOutput,inputs,publicInputs,layers.length].flatMap (encodeLE 8) ++
    layers.flatMap (layerBytes encode)

def pairLayer (d q : ℕ) : Layer F :=
  ⟨2*(d+q),(stream (pairRows (F := F) d q)).map
    (Term.map Fin.val (fun wire => (wireIndex d q wire).val))⟩

/-- The runtime builds from leaves upwards and reverses once at the end.
The recursion below therefore emits the rootward reductions first. -/
def reductions : {d q : ℕ} → Shape d q → List (Layer F)
  | _, _, .root => []
  | d, q, .pair rest => reductions rest ++ [pairLayer d q]

def adapterLayers {d q : ℕ} (shape : Shape d q) (inputs : ℕ)
    (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) : List (Layer F) :=
  ⟨4,(stream (finalRows targets)).map
    (Term.map Fin.val (fun wire => (wireIndex 1 1 wire).val))⟩ ::
    reductions shape ++
      [⟨inputs,(stream (leafRows sources pads powers base masked)).map (Term.map Fin.val id)⟩]

def adapterBytes {d q : ℕ} (encode : F → Bytes) (shape : Shape d q)
    (inputs publicInputs : ℕ) (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) : Bytes :=
  circuitBytes true 16 encode 2 1 inputs publicInputs
    (adapterLayers shape inputs sources pads powers base masked targets)

/-- Only this final hash operation remains abstract. It may be instantiated
with SHA-256, as in Rust, or with the identifier oracle in the proof model. -/
def adapterId {d q : ℕ} (hash : Bytes → Digest) (encode : F → Bytes) (shape : Shape d q)
    (inputs publicInputs : ℕ) (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) : Digest :=
  hash (adapterBytes encode shape inputs publicInputs sources pads powers base masked targets)

theorem adapter_layers_count {d q : ℕ} (shape : Shape d q) (inputs : ℕ)
    (sources : Fin d → ℕ) (pads : Fin 2 → Fin q → ℕ)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ)
    (masked : Fin 2 → Fin q → Bool) (targets : Fin 2 → Fˣ) :
    (adapterLayers shape inputs sources pads powers base masked targets).length =
      (reductions (F := F) shape).length+2 := by
  simp [adapterLayers]

end LfzkV2.Current.MetadataIdentifiers
