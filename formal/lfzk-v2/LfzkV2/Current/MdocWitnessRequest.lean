import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.MdocWitness

/-! Request readback followed by the structural hash separation. This interface is
independent of oracle probability and of the concrete runtime configuration. -/
noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace LfzkV2.Current.MdocWitness
open Application ApplicationSetup ConcreteSetup RuntimeAdaptive
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "N" => ZMod Adapter.Mdoc.primeOrder
local notation "Witness" => Selection.Pair B N (BinaryPublic.Original bp) (PrimePublic.Original pp)

/-- The ordinary hash and signature predicates share the selected binary
bits and use only the supplied public request vectors. -/
def Valid (publicBits : Fin binary.nPublic → Bool) (publicPrime : Fin prime.nPublic → N) (w : Witness) : Prop :=
  HashValid {binary with publicBits := publicBits}
    (extractedPrivate {binary with publicBits := publicBits} w.1) ∧
  prime.description.circuit.Satisfies
    (ApplicationViews.primeInputs (binaryWithBits bp publicBits) (primeWithInputs pp publicPrime) w)

variable {g : Geometry} {fields : Fields} {Advice C Salt : Type} {k s n t : ℕ}
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary.description prime.description P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt))
variable (binaryCount : shape.binaryPublic = binary.nPublic) (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
local notation "W" => CanonicalRuntime.wirePublic bp pp P R repr shape setup cfg
local notation "earlier" => CanonicalRuntime.earlier bp pp P R repr shape setup cfg binaryCount metadata
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime.description P R
  (CanonicalRuntime.wirePublic binary.description prime.description P R repr shape setup cfg))
variable [Inhabited (RuntimeVerifier.Family binary.description prime.description P R
  (CanonicalRuntime.wirePublic binary.description prime.description P R repr shape setup cfg)).Leaf]

theorem valid_at_request
    (output : CanonicalRuntime.Output (Advice := Advice) bp shape)
    (H : CanonicalRuntime.Point bp repr shape setup → Digest × C)
    (decoded : RuntimeVerifier.Decoded bp pp P R W)
    (found : RuntimeAdaptiveVerifier.decode bp pp P R W earlier
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic bp pp P R repr shape setup cfg primeCount) draw output H = some decoded)
    (w : Witness) (truth : decoded.application.True w) :
    Valid binary prime output.request.publicBits
      (CanonicalRuntime.primeInputs bp pp P R repr shape setup cfg primeCount output.request) w := by
  obtain ⟨nd,bd,_,_,hash,signature⟩ := CanonicalRuntime.decoded_true_at_request
    bp pp P R repr shape setup cfg binaryCount primeCount metadata draw output H decoded found w truth
  refine ⟨?_,signature⟩
  exact hashValid_of_satisfies {binary with publicBits := output.request.publicBits} w.1 bd.entries hash

end LfzkV2.Current.MdocWitness
