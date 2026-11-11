import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalPublic
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation

/-! Canonical frontend setup shared by honest execution and public simulation.
The samplers and public prefix writer are operational constructors; neither
requires a simulator correctness, privacy or acceptance proof. Namespace names
are retained so existing callers use the same setup API. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteSimulator
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH
open Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public
  (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
  binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)

local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic

def samples : ConcreteMetadata.Samples B C where
  binary := cfg.binaryDecode
  binaryNonzero := cfg.binaryNonzero
  prime := cfg.primeDecode
  primeNonzero := cfg.primeNonzero
  conversion := cfg.conversion
  fallback := cfg.fallback

def base (request : Request) (root : Digest) :
    CompleteSimulation.BaseWriter binary prime primePlan
      (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic) (C := C) :=
  CompleteWire.canonicalBase shape (⟨0,by decide⟩ : MdocAdvice.Value) repr setup
    binary.description.nPublic
    (CanonicalRuntime.binaryRequest binary.description prime
      (ConcreteSetup.backend binaryNodes binary.description.cells)
      (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg)
      binaryCount) metadata request root

end LfzkV2.Current.ZeroKnowledge.CompleteSimulator
