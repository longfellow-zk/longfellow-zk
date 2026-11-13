import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation

/-! The operational conversion from honest binary sumcheck pads to the
fixed binary circuit payload. Both honest execution and its distribution
proof use this same constructor; the honest path does not import those proofs.
The existing namespace is retained for callers of the conversion. -/
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

def binaryMessageEquiv
    (_native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B) :
    CircuitTape binary.description.circuit ≃ Layered.Replay.Payload binary.description.circuit :=
  circuitEquiv (CompleteTranscript.reader .binary (Equiv.refl B) samples.binary samples.binaryNonzero base H)
    binary.plan inputs 0 (CompleteSimulation.binaryStart binary prime primePlan converted advice)

theorem binaryMessageEquiv_actual
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B)
    (pads : CircuitTape binary.description.circuit) :
    binaryMessageEquiv binary prime primePlan samples base H native converted advice inputs pads =
      realCircuit (CompleteTranscript.reader .binary (Equiv.refl B) samples.binary samples.binaryNonzero base H)
        binary.plan inputs 0 (CompleteSimulation.binaryStart binary prime primePlan converted advice) pads :=
  rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteCoupling
