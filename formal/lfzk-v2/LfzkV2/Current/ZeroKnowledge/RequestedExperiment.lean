import LfzkV2.Current.ZeroKnowledge.RequestedSimulator
import LfzkV2.Current.ZeroKnowledge.HonestRuntime

/-! Complete honest and simulated observer experiments at the request
selected by the prior observer. Public input values are installed by direct
constructors. The honest witness is an input only to the honest experiment;
the simulated experiment receives independent public simulator coins. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.RequestedExperiment
open Application ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

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
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

def honestTape (request : Request) (coins : HonestRuntime.Tape binary prime binaryNodes) :
    HonestRuntime.Tape (RequestedSimulator.requestedBinary binary prime primePlan shape request)
      (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) binaryNodes where
  frontend := {
    prime := coins.frontend.prime
    mask := coins.frontend.mask
    otp := coins.frontend.otp
    binary := coins.frontend.binary
    packing := coins.frontend.packing }
  selectors := coins.selectors
  backend := coins.backend
  nonces := coins.nonces

def honestTapeEquiv (request : Request) : HonestRuntime.Tape binary prime binaryNodes ≃
    HonestRuntime.Tape (RequestedSimulator.requestedBinary binary prime primePlan shape request)
      (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) binaryNodes where
  toFun := honestTape binary prime primePlan binaryNodes shape primeCount request
  invFun coins := {
    frontend := {
      prime := coins.frontend.prime
      mask := coins.frontend.mask
      otp := coins.frontend.otp
      binary := coins.frontend.binary
      packing := coins.frontend.packing }
    selectors := coins.selectors
    backend := coins.backend
    nonces := coins.nonces }
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq B] in
theorem logical_requested (request : Request) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → Adapter.Mdoc.P) (coins : HonestRuntime.Tape binary prime binaryNodes) :
    HonestRuntime.logical (RequestedSimulator.requestedBinary binary prime primePlan shape request)
        (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) binaryNodes
        original remaining (honestTape binary prime primePlan binaryNodes shape primeCount request coins) =
      HonestRuntime.logical binary prime binaryNodes original remaining coins := rfl

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def honestForRequest (request : Request) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → Adapter.Mdoc.P) (coins : HonestRuntime.Tape binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :=
  HonestRuntime.prove
    (RequestedSimulator.requestedBinary binary prime primePlan shape request)
    (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) primePlan binaryNodes repr shape setup
    (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
    binaryCount primeCount metadata draw original remaining
    (honestTape binary prime primePlan binaryNodes shape primeCount request coins) request HM H

def simulatedForRequest (coins : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C) :
    Option Output × ((Bytes → Digest) × (Point → Digest × C)) :=
  match RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount
      metadata draw request HM H coins with
  | none => (none,(HM,H))
  | some result => (some result.1,(HM,result.2))

variable {Observed : Type} {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

def honest (original : Request → Fin binary.nPrivate → Bool)
    (remaining : Request → Fin prime.remaining → Adapter.Mdoc.P)
    (coins : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest) (H : Point → Digest × C) :=
  Observer.experiment prior (fun request =>
    honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      request (original request) (remaining request) coins) after HM H

def simulated (coins : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :=
  Observer.experiment prior
    (simulatedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw coins)
    after HM H

end LfzkV2.Current.ZeroKnowledge.RequestedExperiment
