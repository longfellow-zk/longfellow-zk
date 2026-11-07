import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalSimulation
import LfzkV2.Current.ZeroKnowledge.FrontendSetupAnswerTape

/-! Later frontend stages preserve every earlier challenge answer. These
relations connect the compiler at each stage to the final canonical answer
tape, without reconstructing either circuit from a semantic certificate. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationAnswers

open SumcheckV2 ApplicationSetup ConcreteSetup AnswerTape
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
theorem prime_tail
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (payload : Layered.Replay.Payload prime.circuit) :
    Extends samples.fallback
      (readSetup (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
        primePlan prime.setup.plan payload state false).2
      (CompleteSimulation.primePrefix binary prime primePlan samples base H state payload).state := by
  exact (step_extends base H samples.fallback _).trans (step_extends base H samples.fallback _)

omit [Fintype B] [DecidableEq B] in
theorem conversion
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C) (mu : P) :
    Extends samples.fallback native.state
      (CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu).state := by
  exact (bind_extends samples.fallback native.state _).trans (step_extends base H samples.fallback _)

omit [DecidableEq B] in
theorem binary_read
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template) :
    Extends samples.fallback converted.state
      (CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload).2 := by
  erw [SimulationWrites.binary_state]
  exact (bind_extends samples.fallback converted.state _).trans (execute_extends base H .binary (Equiv.refl B) samples.fallback _ _)

omit [DecidableEq B] in
theorem binary_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
      (simulateCircuit prime.circuit coins.prime)
    let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native coins.mu
    let binaryRead := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted coins.advice
      (simulateCircuit binary.description.template coins.binary)
    Extends samples.fallback binaryRead.2
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (bind_extends samples.fallback _ _).trans
    ((step_extends base H samples.fallback _).trans (bind_extends samples.fallback _ _))

omit [DecidableEq B] in
theorem converted_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
      (simulateCircuit prime.circuit coins.prime)
    let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native coins.mu
    Extends samples.fallback converted.state
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (binary_read binary prime primePlan samples base H _ _ _ _).trans
    (binary_future binary prime primePlan samples base H context coins)

omit [DecidableEq B] in
theorem native_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
      (simulateCircuit prime.circuit coins.prime)
    Extends samples.fallback native.state
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (conversion binary prime primePlan samples base H _ _).trans
    (converted_future binary prime primePlan samples base H context coins)

omit [DecidableEq B] in
theorem prime_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
    let payload := simulateCircuit prime.circuit coins.prime
    Extends samples.fallback
      (readSetup (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
        primePlan prime.setup.plan payload selected false).2
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (prime_tail binary prime primePlan samples base H _ _).trans
    (native_future binary prime primePlan samples base H context coins)

omit [DecidableEq B] in
theorem selected_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    Extends samples.fallback
      (CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints)
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (readSetup_extends base H .prime (Equiv.refl P) samples.prime samples.primeNonzero samples.fallback
    primePlan prime.setup.plan (simulateCircuit prime.circuit coins.prime) _ false).trans
      (prime_future binary prime primePlan samples base H context coins)

omit [DecidableEq B] in
theorem first_future (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    Extends samples.fallback
      (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).2
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state := by
  exact (bind_extends samples.fallback _ _).trans
    (selected_future binary prime primePlan samples base H context coins)

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationAnswers
