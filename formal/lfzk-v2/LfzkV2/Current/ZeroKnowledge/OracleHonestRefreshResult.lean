import LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh

/-! Project the source result before exposing a concrete observer context.
The request index remains exact; none of these laws executes the source
program or assumes that its parser succeeds. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxRecDepth 4096

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic

local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (tape : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

local notation "b" => RequestedSimulator.requestedBinary binary prime primePlan shape
local notation "p" => RequestedSimulator.requestedPrime binary prime primePlan shape primeCount
local notation "configuration" => RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount
local notation "source" => RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount

variable {Context : Type}
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)

theorem finish_next_at (sample : Fin 361 → B) (context : Context)
    (baseH returnedH : Point → Digest × C) :
    let request := requestOf context
    finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw
        sample ((next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf
          sample context).run baseH).1 returnedH =
      (OracleHonestTree.asPending (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
        binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample
        ((OracleHonestTree.tree (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
          binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample).run baseH).1).map
        (OracleHonestRuntime.finish (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
          binaryCount metadata (original request) (remaining request) (source request tape) request HM returnedH sample) := by
  rw [next_output]
  rfl

theorem active_next_at (sample : Fin 361 → B) (context : Context) (baseH : Point → Digest × C) :
    let request := requestOf context
    active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw
        sample ((next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf
          sample context).run baseH).1 ↔
      (OracleHonestTree.asPending (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
        binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample
        ((OracleHonestTree.tree (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
          binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample).run baseH).1).isSome := by
  rw [next_output]
  rfl

theorem input_next_at (sample : Fin 361 → B) (context : Context) (baseH : Point → Digest × C) :
    let request := requestOf context
    input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM
        sample ((next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf
          sample context).run baseH).1 =
      OracleHonestTree.input (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
        binaryCount metadata (original request) (remaining request) (source request tape) request HM sample
        ((OracleHonestTree.tree (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
          binaryCount primeCount metadata (original request) (remaining request) (source request tape) request HM draw sample).run baseH).1 := by
  rw [next_output]
  rfl

end LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
