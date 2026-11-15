import LfzkV2.Current.ZeroKnowledge.FrontendCompletePayload

/-! Coin changes at the actual causal frontend stages. These preserve the
whole public state, not merely polynomial marginals: compiler output, later
metadata and subsequent oracle keys are deterministic functions of the same
preserved payloads. No abstract reader-agreement or privacy premise occurs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteCoupling
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def primeEquiv (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (inputs : Cube prime.input → P) : CircuitTape prime.circuit ≃ CircuitTape prime.circuit :=
  circuitCoupling (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan inputs 0 state

theorem primeEquiv_payload
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (inputs : Cube prime.input → P) (pads : CircuitTape prime.circuit) :
    simulateCircuit prime.circuit (primeEquiv binary prime primePlan samples base H state inputs pads) =
      realCircuit (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
        primePlan inputs 0 state pads := circuitCoupling_view _ _ _ _ _ _

def alphas (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C) : Adapter.Mdoc.Alphas :=
  fun mu => (CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu).alpha

def adapterEquiv (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (shared : Fin 768 → Bool) : (P × (Fin 2 → AdapterBits.RawWord)) ≃ ((P × MdocAdvice.Value) × AdapterBits.Unused) :=
  Adapter.Mdoc.coupling native.claim.sharedWeights shared native.eta.val
    (alphas binary prime primePlan samples base H native)

def binaryEquiv
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B) :
    CircuitTape binary.description.circuit ≃ CircuitTape binary.description.circuit :=
  (binaryMessageEquiv binary prime primePlan samples base H native converted advice inputs).trans
    (circuitPayloadEquiv binary.description.circuit).symm

theorem binaryEquiv_payload
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B)
    (pads : CircuitTape binary.description.circuit) :
    simulateCircuit binary.description.circuit
        (binaryEquiv binary prime primePlan samples base H native converted advice inputs pads) =
      binaryMessageEquiv binary prime primePlan samples base H native converted advice inputs pads :=
  (circuitPayloadEquiv binary.description.circuit).apply_symm_apply _

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteCoupling
