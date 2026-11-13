import LfzkV2.Current.ZeroKnowledge.FrontendHistory
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation

/-! Every public frontend stage preserves the exact write/link/answer
history. The proof follows the existing protocol stages, with no additional
queries and no complete-body input to the generator. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationHistory

open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical

variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
theorem selected_good (context : Key) (fingerprints : Current.Fingerprints (MdocRuntime.fields B)) :
    History.Good base H context
      (CompleteSimulation.selectedState binary prime primePlan samples base H context fingerprints) := by
  apply History.bind_good
  apply History.step_good
  exact History.initial_good base H context samples.fallback

omit [Fintype B] [DecidableEq B] in
theorem prime_good (context : Key)
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (payload : Layered.Replay.Payload prime.circuit) (good : History.Good base H context state) :
    History.Good base H context
      (CompleteSimulation.primePrefix binary prime primePlan samples base H state payload).state := by
  apply History.step_good
  exact History.circuit_good base H .prime (Equiv.refl P) samples.prime samples.primeNonzero
    primePlan prime.setup.plan payload false context state good

omit [Fintype B] [DecidableEq B] in
theorem conversion_good (context : Key)
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C) (mu : P)
    (good : History.Good base H context native.state) :
    History.Good base H context
      (CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu).state := by
  apply History.step_good
  exact History.bind_good base H context native.state _ good

omit [Fintype B] [DecidableEq B] in
theorem binary_good (context : Key)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.circuit)
    (good : History.Good base H context converted.state) :
    History.Good base H context
      (CompleteSimulation.binaryReplay binary prime primePlan samples base H converted advice payload).2 := by
  apply History.circuit_good
  exact History.bind_good base H context converted.state _ good

omit [DecidableEq B] in
theorem simulate_good (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    History.Good base H context
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  apply History.bind_good
  apply History.step_good
  apply History.bind_good
  apply binary_good
  apply conversion_good
  apply prime_good
  exact selected_good binary prime primePlan samples base H context coins.fingerprints

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationHistory
