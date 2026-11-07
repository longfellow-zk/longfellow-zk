import LfzkV2.Current.ZeroKnowledge.MdocPublicSetup
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeSatisfaction
import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling
import LfzkV2.Current.ZeroKnowledge.FrontendHonestAdapter

/-! Ordinary mdoc witnesses supply the trusted application-circuit facts.
The hash relation below concerns only non-adapter checks. It keeps the
document's private prefix fixed and permits every value of the reserved
256-bit mask and twenty OTP bits, and every generated-adapter parameter.
Thus it includes the intended noninterference of the trusted hash checks
from that suffix and from generated adapter wires. This property is not
inferred from an arbitrary `BinaryCircuit` topology. The two adapter
assertions, all protocol rows and all runtime decoding facts are derived
by the existing correctness proofs.

Every runtime consequence is pointwise at one public request/prefix. There
is no validity requirement for a request the observer cannot return. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocWitness
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Algebra (ZMod 2) B]

/-- The trusted ordinary hash relation, uniformly in the adapter-only
inputs and parameters. It assumes no generated product equation. -/
def HashValid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool) : Prop :=
  ∀ (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (powers : Fin 2 → Fin 1024 → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin 10 → Bool) (targets : Fin 2 → Bˣ),
    Hash.Checks binary.description.layout binary.description.output binary.description.shape binary.description.others
      binary.description.carry binary.description.above binary.description.sources binary.description.advice
      powers base masked targets
      (Current.Adapter.Circuit.bitValue ∘ CompleteInputs.bits binary
        (CompleteInputs.privateValues binary original mask otp))

theorem private_prefix (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin binary.nPrivate)
    (before : i.val < binary.nPrivate-276) :
    CompleteInputs.privateValues binary original mask otp i = original i :=
  dif_pos before

section Frontend
variable [Fintype B] [DecidableEq B]
variable {Key Base C : Type}
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
theorem coupling_hash (context : Key) (original : Fin binary.nPrivate → Bool) (valid : HashValid binary original)
    (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (Adapter.Mdoc.P × MdocAdvice.Value) × Fin 16) :
    FullCoupling.hashChecks binary prime primePlan samples base H context original responses coin converted := by
  unfold FullCoupling.hashChecks FullCoupling.recoveredPrivate CompleteInputs.recoveredPrivate
  exact valid _ _ _ _ _ _

omit [Fintype B] [DecidableEq B] in
theorem honest_hash (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (valid : HashValid binary original)
    (tape : CompleteHonest.Tape binary prime) :
    HonestAdapter.hashChecks binary prime primePlan samples base H native original tape := by
  unfold HonestAdapter.hashChecks CompleteHonest.privateBits
  exact valid _ _ _ _ _ _

end Frontend

section Runtime
variable [Fintype B] [DecidableEq B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
variable (SHA : Bytes → Digest)

local notation "Setup" => MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
local notation "Cfg" => MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA
local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
  (by change 128 < 2^64; decide)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Meta" => MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA
local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Answer" => MdocRuntime.Answer binary.description prime.description binary.plan prime.plan Nodes
local notation "bCount" => RuntimeStatement.binary_count binary prime.description prime.plan bounds.inputFits bounds.privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits

omit [DecidableEq B] in
theorem configuration_runtime : Cfg =
    RuntimeStatement.configuration binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits Setup := rfl

variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin prime.description.remaining → Adapter.Mdoc.P)
variable (H : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide))
  (MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA) binary.nPublic →
  Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))

local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Point" => QueryRuntime.Runtime.Point Repr Sh Setup binary.nPublic
local notation "Prefix" => Request × List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × Answer))
local notation "Coins" => CompleteHonest.Tape binary prime.description × CompleteHonest.Masks (B := B)

omit [DecidableEq B] in
theorem backend_hash (earlier : Prefix) (labels : Fin (2*2443-1) → Digest)
    (valid : HashValid (RequestedSimulator.requestedBinary binary prime.description prime.plan Sh earlier.1) (original earlier.1)) :
    BackendRuntime.hashChecks binary prime.description prime.plan Nodes Repr Sh Setup Cfg bCount pCount Meta original H earlier labels := by
  unfold BackendRuntime.hashChecks
  dsimp only
  intro responses coin converted
  apply coupling_hash
  exact valid

omit [DecidableEq B] in
theorem runtime_hash (coins : Coins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest)
    (valid : HashValid (RequestedSimulator.requestedBinary binary prime.description prime.plan Sh earlier.1) (original earlier.1)) :
    BackendRuntimeSatisfaction.hashTruth binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits Setup
      Meta original remaining H coins earlier labels := by
  unfold BackendRuntimeSatisfaction.hashTruth
  dsimp only
  apply honest_hash
  exact valid

theorem satisfied (coins : Coins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (hash : HashValid (RequestedSimulator.requestedBinary binary prime.description prime.plan Sh earlier.1) (original earlier.1))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime.description prime.plan Sh earlier.1
      let p := RequestedSimulator.requestedPrime binary prime.description prime.plan Sh pCount earlier.1
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original earlier.1) (remaining earlier.1))) :
    (BackendRuntime.statements binary prime.description prime.plan Nodes Repr Sh Setup Cfg bCount pCount Meta original remaining H coins earlier labels).1.Satisfies
      (Backend.logical (BackendRuntime.cells binary prime.description prime.plan Nodes Repr Sh Setup original remaining coins earlier).1) ∧
    (BackendRuntime.statements binary prime.description prime.plan Nodes Repr Sh Setup Cfg bCount pCount Meta original remaining H coins earlier labels).2.Satisfies
      (Backend.logical (BackendRuntime.cells binary prime.description prime.plan Nodes Repr Sh Setup original remaining coins earlier).2) := by
  exact BackendRuntimeSatisfaction.satisfied binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits Setup Meta
    original remaining H coins earlier labels pivotOne
    (backend_hash binary prime cantor scalars ids bounds SHA original H earlier labels hash) primitive signature
    (runtime_hash binary prime cantor scalars ids bounds SHA original remaining H coins earlier labels hash)

end Runtime
end LfzkV2.Current.ZeroKnowledge.MdocWitness
