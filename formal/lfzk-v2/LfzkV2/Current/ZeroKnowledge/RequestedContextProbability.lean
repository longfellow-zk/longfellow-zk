import LfzkV2.Current.ZeroKnowledge.RequestedContextProjection
import LfzkV2.Current.ZeroKnowledge.TranscriptOracleProbability

/-! Lift the complete requested-protocol bound to raw transcript-oracle
experiments. Canonicality and normalization are proved for the actual
callbacks. Malformed and repeated observer queries remain in the full
view; one sampled raw table supplies all their answers on each side. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedContextProbability
open Application ApplicationSetup ConcreteSetup Frontend LigeroFamily
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
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
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "codec" => QueryRuntime.Runtime.codec repr shape setup binary.description.nPublic fits
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic

variable [Fintype C]
local instance pointFintype : Fintype (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) := inferInstance
variable {R S : Type} [Fintype R] [Fintype S] [Nonempty R] [Nonempty S]
variable (realTape : R → HonestRuntime.Tape binary prime binaryNodes)
variable (simulateTape : S → CompleteSimulator.Tape (C := C) binary prime binaryNodes)
variable (realHM : R → Bytes → Digest) (simulateHM : S → Bytes → Digest)
variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (pivotOne : binary.basis 0 = 1)
variable (hash : ∀ coin (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) (outside : Bytes → Digest × C),
  OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining (realTape coin) (realHM coin)
    (requestOf (Observer.run (realHM coin) ((QueryRuntime.Runtime.codec repr shape setup binary.description.nPublic fits).oracle outside H) prior).1) H
    (OracleHonestRuntimeNormalization.maskSample binary prime binaryNodes (realTape coin)))

include bodyFits hash pivotOne in
/-- The only statistical premise is the complete typed-protocol bound.
The literal honest/simulator projection, preservation of aborts and oracle
updates, and reconstruction of arbitrary raw observer traces are derived
here. The final protocol theorem instantiates this helper with its proved
typed aggregate and concrete oracle marginals. Honest-witness validity is
needed only at actual outputs of the observer prefix. -/
theorem window_statClose (defaultAnswer : Digest × C) (rawFallback : Bytes → Digest × C)
    (window : Finset Bytes) (covers : ∀ point : {point : Point // QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic point},
      (codec).encode point ∈ window)
    {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (typed : ∀ outside : Bytes → Digest × C, StatClose epsilon
      (fun coin : R × (Point → Digest × C) =>
        RequestedContextExperiment.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          requestOf ((codec).program outside prior) (fun request proof => (codec).program outside (after request proof))
          original remaining (realTape coin.1) (realHM coin.1) coin.2)
      (fun coin : S × (Point → Digest × C) =>
        RequestedContextExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          requestOf ((codec).program outside prior) (fun request proof => (codec).program outside (after request proof))
          (simulateTape coin.1) (simulateHM coin.1) coin.2)) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ window} → Digest × C) =>
        RequestedContextExperiment.rawHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          requestOf prior after fits fallback original remaining (realTape coin.1) (realHM coin.1)
          (OracleWindow.extend window coin.2 rawFallback))
      (fun coin : S × ({raw // raw ∈ window} → Digest × C) =>
        RequestedContextExperiment.rawSimulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          requestOf prior after fits fallback (simulateTape coin.1) (simulateHM coin.1)
          (OracleWindow.extend window coin.2 rawFallback)) := by
  let real := fun coin : R => RequestedContextExperiment.rawHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    requestOf prior after fits fallback original remaining (realTape coin) (realHM coin)
  let simulate := fun coin : S => RequestedContextExperiment.rawSimulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    requestOf prior after fits fallback (simulateTape coin) (simulateHM coin)
  have each (outside : Bytes → Digest × C) : StatClose epsilon
      (fun coin : R × (Point → Digest × C) => real coin.1 ((codec).oracle outside coin.2))
      (fun coin : S × (Point → Digest × C) => simulate coin.1 ((codec).oracle outside coin.2)) := by
    have lifted := ObserverStatefulRaw.statClose codec requestOf prior after outside (fun _ => 0) defaultAnswer realHM simulateHM
      (fun coin request => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        request (original request) (remaining request) (realTape coin))
      (fun coin => RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        (simulateTape coin)) (typed outside)
    have real_eq : (fun coin : R × (Point → Digest × C) => real coin.1 ((codec).oracle outside coin.2)) =
        (fun coin : R × (Point → Digest × C) => ObserverStatefulRaw.rawExperiment codec requestOf prior
          (fun request => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
            request (original request) (remaining request) (realTape coin.1)) after outside (realHM coin.1) coin.2) := by
      funext coin
      exact RequestedContextProjection.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        requestOf prior after fits fallback bodyFits outside (realHM coin.1) coin.2 original remaining (realTape coin.1) pivotOne (hash coin.1 coin.2 outside)
    have simulate_eq : (fun coin : S × (Point → Digest × C) => simulate coin.1 ((codec).oracle outside coin.2)) =
        (fun coin : S × (Point → Digest × C) => ObserverStatefulRaw.rawExperiment codec requestOf prior
          (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
            (simulateTape coin.1)) after outside (simulateHM coin.1) coin.2) := by
      funext coin
      exact RequestedContextProjection.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        requestOf prior after fits fallback bodyFits outside (simulateHM coin.1) coin.2 (simulateTape coin.1)
    rw [real_eq,simulate_eq]
    exact lifted
  exact TranscriptOracleProbability.window_statClose_full codec window covers defaultAnswer rawFallback nonnegative real simulate each

end LfzkV2.Current.ZeroKnowledge.RequestedContextProbability
