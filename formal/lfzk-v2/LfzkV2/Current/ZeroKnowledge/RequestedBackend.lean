import LfzkV2.Current.ZeroKnowledge.RequestedSimulator
import LfzkV2.Current.ZeroKnowledge.CompleteResponse
import LfzkV2.Current.ZeroKnowledge.CompleteObserver

/-! Backend reconstruction reads the public request from the transcript.
Installing those same public values in frontend records does not change the
backend parser, batching coins, responses or completion. These equalities
are proved before any concrete frontend computation is substituted. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedBackend
open Application ApplicationSetup ConcreteSetup Frontend RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic

local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)
local notation "Leaf" => MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
  MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0

theorem statement (request : Request) (frontend : Body) (H : Point → Digest × C) :
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    CompleteCanonicalVerifier.statementAt b.description p binaryNodes ConcreteSetup.primeNodes repr shape setup config
      binaryCount primeCount metadata request frontend H =
    CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata request frontend H := rfl

theorem batching (draw : C → RuntimeVerifier.RawSamples binary.description prime P R Public)
    (request : Request) (frontend : Body) (H : Point → Digest × C) :
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    CompleteCanonicalVerifier.batchingCoin b.description p binaryNodes ConcreteSetup.primeNodes repr shape setup config
      binaryCount metadata draw request frontend H =
    CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata draw request frontend H := rfl

theorem responses (request : Request)
    (logical : Backend.Cells B (rows binary.description.cells) 265 ×
      Backend.Cells Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (tape : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) :
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let requestedPublic := CompleteCanonicalVerifier.publicConfig b.description p binaryNodes ConcreteSetup.primeNodes repr shape setup config
    CompleteResponse.realResponses b.description p binaryNodes ConcreteSetup.primeNodes requestedPublic logical statement coin tape =
      CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public logical statement coin tape := rfl

theorem complete (request : Request) (indices : Fin 84 ↪ Fin 2443) (frontend : Body)
    (responses : JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opening : OpeningView 2443 (OrderedOpening.query indices).coordinates Digest Digest)
    (H : Point → Digest × C) (answer : Digest × C) :
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    CompleteObserver.complete b.description p binaryNodes ConcreteSetup.primeNodes repr shape setup config
      binaryCount primeCount metadata request indices frontend responses columns opening H answer =
    CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata request indices frontend responses columns opening H answer := rfl

end LfzkV2.Current.ZeroKnowledge.RequestedBackend
