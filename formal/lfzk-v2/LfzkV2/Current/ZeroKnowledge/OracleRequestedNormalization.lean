import LfzkV2.Current.ZeroKnowledge.OracleSimulatorNormalization
import LfzkV2.Current.ZeroKnowledge.OracleHonestRuntimeNormalization
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshGames
import LfzkV2.Current.ZeroKnowledge.RequestedExperiment

/-! Canonical-coordinate normalization for both literal application
callbacks at the public request selected by the observer. The complete
public proof and Merkle oracle are preserved; only canonical coordinates
of the returned transcript oracle are compared. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRequestedNormalization
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend
open scoped Classical
set_option maxHeartbeats 1400000
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
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)
variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
variable (agree : OracleNormalization.Agree repr shape setup binary.description.nPublic H H')

abbrev ResultEq
    (first second : Option Output × ((Bytes → Digest) × (Point → Digest × C))) : Prop :=
  OracleResults.Same
    {point | QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic point} first second

/-- The application callback only totalizes a partial completion. In
particular, a failed parse retains both original oracle functions. -/
theorem simulated_totalize (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape request HM H =
      OracleResults.totalize HM H
        (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape) := by
  unfold RequestedExperiment.simulatedForRequest OracleResults.totalize
  cases RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape <;> rfl

include agree bodyFits in
theorem simulated_eq (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    ResultEq binary prime primePlan repr shape setup
      (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape request HM H)
      (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape request HM H') := by
  have completed := OracleSimulatorNormalization.simulate_eq
    (RequestedSimulator.requestedBinary binary prime primePlan shape request)
    (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) primePlan binaryNodes repr shape setup
    (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
    binaryCount primeCount metadata draw request HM
    (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape) H H' bodyFits agree
  change OracleCompleteNormalization.CompletionEq
    (RequestedSimulator.requestedBinary binary prime primePlan shape request).description repr shape setup
    (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape)
    (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H' tape) at completed
  have publicCompletion : OracleResults.SameCompletion
      {point : Point | QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic point}
      (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H tape)
      (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request HM H' tape) :=
    completed.mono (fun _ canonical => canonical)
  rw [simulated_totalize,simulated_totalize]
  exact publicCompletion.totalize HM H H' (fun point canonical => agree point canonical)

include agree bodyFits in
theorem honest_eq (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      (fun _ => original) (fun _ => remaining) tape HM request H (OracleHonestRuntimeNormalization.maskSample binary prime binaryNodes tape)) :
    ResultEq binary prime primePlan repr shape setup
      (RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request original remaining tape HM H)
      (RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw request original remaining tape HM H') := by
  have same := OracleHonestRuntimeNormalization.prove_original_eq
    (RequestedSimulator.requestedBinary binary prime primePlan shape request)
    (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) primePlan binaryNodes repr shape setup
    (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
    binaryCount metadata original remaining (RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape)
    request HM primeCount H H' draw bodyFits agree pivotOne hash
  exact ⟨same,rfl,fun point canonical => agree point canonical⟩

end LfzkV2.Current.ZeroKnowledge.OracleRequestedNormalization
