import LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh

/-! The complete abort-aware opening refresh for a request chosen by an
arbitrary earlier oracle program. The honest side uses the literal source
frontend, authentication and final seal. The programmed side draws one full
independent answer and returns the updated oracle for all later observation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

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
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)

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

variable {Context View : Type} {preT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)
variable (before : Tree (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Context preT)
variable (observe : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) → View)

def hashChecks (request : Request) (H : Point → Digest × C) (sample : Fin 361 → B) : Prop :=
  ∀ responses coin converted, FullCoupling.hashChecks (b request) (p request) primePlan
    (CompleteSimulator.samples (b request) (p request) primePlan binaryNodes repr shape setup (configuration request))
    (OracleHonestCanonical.writer (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
      binaryCount metadata (original request) (remaining request) (source request tape) request HM sample) H
    (FingerprintPrefix.context request (OracleHonestCanonical.root (b request) (p request) primePlan binaryNodes repr shape setup (configuration request)
      (original request) (remaining request) (source request tape) HM sample))
    (original request) responses coin converted

/-- The honest observation is the actual complete source prover, including
its parser abort, authentication tree and ordinary final seal. -/
theorem finish_next (sample : Fin 361 → B) (context : Context) (H : Point → Digest × C)
    (pivotOne : binary.basis 0 = 1)
    (hash : hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape HM (requestOf context) H sample) :
    finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw
      sample ((next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf sample context).run H).1 H =
      (RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        (requestOf context) (original (requestOf context)) (remaining (requestOf context))
        (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample) HM H).1 := by
  rw [next_output]
  unfold finish
  dsimp only
  rw [OracleHonestTree.pending_output (b (requestOf context)) (p (requestOf context)) primePlan binaryNodes repr shape setup (configuration (requestOf context))
    binaryCount primeCount metadata (original (requestOf context)) (remaining (requestOf context)) (source (requestOf context) tape)
    (requestOf context) HM draw H sample pivotOne hash]
  exact (OracleHonestRuntime.prove_pending (b (requestOf context)) (p (requestOf context)) primePlan binaryNodes repr shape setup (configuration (requestOf context))
    binaryCount primeCount metadata (original (requestOf context)) (remaining (requestOf context)) (source (requestOf context) tape)
    (requestOf context) HM H draw sample).symm

def programmed (coin : (Fin 361 → B) × ((Point → Digest × C) × (Digest × C))) : View :=
  OracleRefreshProbability.programmed
    (OracleRefreshPrior.program before (next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf))
    (OracleRefreshPrior.target (fun sample (_ : Context) => input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM sample))
    (OracleRefreshPrior.enabled (fun sample (_ : Context) => active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw sample))
    (observation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw observe) coin

def honest (coin : (Fin 361 → B) × ((Point → Digest × C) × (Digest × C))) : View :=
  OracleRefreshProbability.honest
    (OracleRefreshPrior.program before (next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw requestOf))
    (OracleRefreshPrior.target (fun sample (_ : Context) => input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM sample))
    (OracleRefreshPrior.enabled (fun sample (_ : Context) => active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw sample))
    (observation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape HM draw observe) coin

end LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh
