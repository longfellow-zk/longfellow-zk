import LfzkV2.Current.ZeroKnowledge.OracleRequestedNormalization
import LfzkV2.Current.ZeroKnowledge.OracleRawNormalization

/-! The full raw observer experiment is unchanged by auxiliary typed
oracle coordinates. This covers the actual requested honest and simulated
callbacks, complete public proofs, malformed/repeated raw calls and the
returned oracles used by the later observer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRequestedRawNormalization
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend
open scoped Classical
set_option maxHeartbeats 1200000
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
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)
variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
variable (agree : OracleNormalization.Agree repr shape setup binary.description.nPublic H H')

variable {Observed : Type} {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest Bytes (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest Bytes (Digest × C) Observed postM postT)
variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)
variable (outside : Bytes → Digest × C)
local notation "codec" => QueryRuntime.Runtime.codec repr shape setup binary.description.nPublic fits

include agree bodyFits in
theorem simulated_raw_eq (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape) HM H =
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape) HM H' := by
  apply OracleRawNormalization.experiment_eq_of_results codec outside prior after _ HM H H'
    (fun point canonical => agree point canonical)
  intro selected
  exact OracleRequestedNormalization.simulated_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    draw selected HM H H' bodyFits agree tape

include agree bodyFits in
theorem honest_raw_eq
    (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
    (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ selected, OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape HM selected H (OracleHonestRuntimeNormalization.maskSample binary prime binaryNodes tape)) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (fun selected => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        selected (original selected) (remaining selected) tape) HM H =
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (fun selected => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        selected (original selected) (remaining selected) tape) HM H' := by
  apply OracleRawNormalization.experiment_eq_of_results codec outside prior after _ HM H H'
    (fun point canonical => agree point canonical)
  intro selected
  exact OracleRequestedNormalization.honest_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    draw selected HM H H' bodyFits agree (original selected) (remaining selected) tape pivotOne (hash selected)

include agree bodyFits in
theorem honest_raw_eq_at
    (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
    (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape HM (Observer.run HM ((codec).oracle outside H) prior).1 H
      (OracleHonestRuntimeNormalization.maskSample binary prime binaryNodes tape)) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (fun selected => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        selected (original selected) (remaining selected) tape) HM H =
    TranscriptObserverExperiment.rawExperiment codec outside prior after
      (fun selected => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        selected (original selected) (remaining selected) tape) HM H' := by
  apply OracleRawNormalization.experiment_eq_at_result codec outside prior after _ HM H H'
    (fun point canonical => agree point canonical)
  exact OracleRequestedNormalization.honest_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    draw (Observer.run HM ((codec).oracle outside H) prior).1 HM H H' bodyFits agree
    (original _) (remaining _) tape pivotOne hash

end LfzkV2.Current.ZeroKnowledge.OracleRequestedRawNormalization
