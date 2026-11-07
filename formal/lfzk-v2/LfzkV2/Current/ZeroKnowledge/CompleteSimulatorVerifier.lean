import LfzkV2.Current.ZeroKnowledge.CompleteSimulator
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier

/-! Acceptance of successful complete public simulation by the actual runtime
verifier. The simulator constructor does not depend on this theorem. -/
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
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public
  (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)

local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

theorem simulate_accepts (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C)
    (tape : Tape (C := C) binary prime binaryNodes) (result : Output × (Point → Digest × C))
    (completed : simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      request HM H tape = some result) :
    RuntimeAdaptiveVerifier.verify binary.description prime
      (ConcreteSetup.backend binaryNodes binary.description.cells)
      (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) Public
      (CompleteCanonicalVerifier.earlier binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup
        cfg binaryCount metadata) (CanonicalRequest.hashPublic binary.description.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime
        (ConcreteSetup.backend binaryNodes binary.description.cells)
        (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg)
        primeCount) draw
      (CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg)
      HM result.1 result.2 = true :=
  CompleteCanonicalVerifier.complete_success_accepts binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata draw request HM (cfg.sample tape.answer.2) tape.nonces tape.backend
    _ H tape.answer result rfl completed

end LfzkV2.Current.ZeroKnowledge.CompleteSimulator
