import LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment
import LfzkV2.Current.ZeroKnowledge.OracleRequestedNormalization

/-! The literal requested raw experiments project to the proved typed
experiments. Canonical normalization is supplied by the actual honest and
simulated callbacks, rather than a caller-provided correspondence claim. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedContextProjection
open Application ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
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
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

variable {Context Observed : Type} {preM preT postM postT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest Bytes (Digest × C)
  Context preM preT)
variable (after : Context →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest Bytes (Digest × C) Observed postM postT)
variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)
variable (fallback : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
variable (outside : Bytes → Digest × C) (HM : Bytes → Digest)
variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
local notation "codec" => QueryRuntime.Runtime.codec repr shape setup binary.description.nPublic fits

include bodyFits in
theorem simulated (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    RequestedContextExperiment.rawSimulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      requestOf prior after fits fallback tape HM ((codec).oracle outside H) =
    ObserverStatefulRaw.rawExperiment codec requestOf prior
      (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape)
      after outside HM H := by
  unfold RequestedContextExperiment.rawSimulated
  apply ObserverStatefulRaw.projection
  exact OracleRequestedNormalization.simulated_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (requestOf (Observer.run HM ((codec).oracle outside H) prior).1) HM H ((codec).restrict ((codec).oracle outside H) fallback) bodyFits
    (OracleNormalization.normalize_agree repr shape setup binary.description.nPublic fits H fallback outside) tape

include bodyFits in
theorem honest
    (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
    (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape HM (requestOf (Observer.run HM ((codec).oracle outside H) prior).1) H
      (OracleHonestRuntimeNormalization.maskSample binary prime binaryNodes tape)) :
    RequestedContextExperiment.rawHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      requestOf prior after fits fallback original remaining tape HM ((codec).oracle outside H) =
    ObserverStatefulRaw.rawExperiment codec requestOf prior
      (fun request => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        request (original request) (remaining request) tape) after outside HM H := by
  unfold RequestedContextExperiment.rawHonest
  apply ObserverStatefulRaw.projection
  exact OracleRequestedNormalization.honest_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (requestOf (Observer.run HM ((codec).oracle outside H) prior).1) HM H ((codec).restrict ((codec).oracle outside H) fallback) bodyFits
    (OracleNormalization.normalize_agree repr shape setup binary.description.nPublic fits H fallback outside)
    (original _) (remaining _) tape pivotOne hash

end LfzkV2.Current.ZeroKnowledge.RequestedContextProjection
