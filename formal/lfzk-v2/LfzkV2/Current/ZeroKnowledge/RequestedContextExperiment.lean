import LfzkV2.Current.ZeroKnowledge.RequestedExperiment
import LfzkV2.Current.ZeroKnowledge.ObserverStatefulRaw

/-! Literal requested honest and simulated experiments with persistent
private observer context. The prover accesses only canonical encodings. The
observer may make arbitrary raw queries, before and after the proof, to
the same oracle and its actual returned update. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment
open Application ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
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
local notation "codec" => QueryRuntime.Runtime.codec repr shape setup binary.description.nPublic fits

variable (typedPrior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Context preM preT)
variable (typedAfter : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

def honest
    (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
    (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest)
    (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) :=
  ObserverStateful.experiment requestOf typedPrior
    (fun request => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      request (original request) (remaining request) tape) typedAfter HM H

def simulated (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) :=
  ObserverStateful.experiment requestOf typedPrior
    (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape)
    typedAfter HM H

def rawHonest
    (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
    (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest) (H : Bytes → Digest × C) :=
  ObserverStatefulRaw.rawRun codec requestOf prior
    (fun request => RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      request (original request) (remaining request) tape) after fallback HM H

def rawSimulated (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Bytes → Digest × C) :=
  ObserverStatefulRaw.rawRun codec requestOf prior
    (RequestedExperiment.simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw tape)
    after fallback HM H

end LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment
