import LfzkV2.Current.ZeroKnowledge.OracleCompleteNormalization
import LfzkV2.Current.ZeroKnowledge.CompleteSimulator

/-! The actual public simulator ignores noncanonical transcript coordinates.
Only its serialized frontend body is compared across oracles. The existing
canonical completion theorem handles derived claims, parser aborts, backend
responses, the programmed answer and normal final seal. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleSimulatorNormalization
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)

local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)
variable (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
variable (agree : OracleNormalization.Agree repr shape setup binary.description.nPublic H H')

def frontend (oracle : Point → Digest × C) :=
  CompleteFrontendBody.body binary prime primePlan
    (CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg HM tape)
    (CompleteSimulator.frontendResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM oracle tape)

theorem frontend_eq :
    frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM tape H =
    frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM tape H' := rfl

include agree bodyFits in
theorem simulate_eq :
    OracleCompleteNormalization.CompletionEq binary.description repr shape setup
      (CompleteSimulator.simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape)
      (CompleteSimulator.simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H' tape) := by
  have normalized := OracleCompleteNormalization.complete_eq binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata bodyFits request H H' agree draw HM (cfg.sample tape.answer.2) tape.nonces tape.backend
    (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM tape H) tape.answer
  have bodies := frontend_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request HM tape H H'
  have results := congrArg (fun body => CompleteCanonicalVerifier.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata draw request HM (cfg.sample tape.answer.2) tape.nonces tape.backend body H' tape.answer) bodies
  exact (congrArg (OracleCompleteNormalization.CompletionEq binary.description repr shape setup
    (CompleteSimulator.simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape)) results).mp normalized

end LfzkV2.Current.ZeroKnowledge.OracleSimulatorNormalization
