import LfzkV2.Current.ZeroKnowledge.FrontendSimulationAnswers

/-! Read back the row-batching, rescaling, conversion and packing answers
from the final frontend tape. These are the actual existing squeezes; no
new query or semantic row correspondence is supplied to this bridge. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationScalarAnswers

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

omit [DecidableEq B] in
theorem first_values (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    (CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)).1 =
      lookup samples.fallback
        (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state 0 := by
  have inside : 0 < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [SimulationWrites.capacity]
    omega
  exact step_answer_into base H samples.fallback (CompleteTranscript.initial context samples.fallback)
    _ inside (SimulationAnswers.first_future binary prime primePlan samples base H context coins)

omit [Fintype B] [DecidableEq B] in
theorem prime_values
    (state future : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (payload : Layered.Replay.Payload prime.circuit)
    (fits : state.rank.val+HonestTranscript.circuitFuel primePlan false+2 ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length)
    (extended : Extends samples.fallback
      (CompleteSimulation.primePrefix binary prime primePlan samples base H state payload).state future) :
    let read := readSetup (CompleteTranscript.reader .prime (Equiv.refl P)
      samples.prime samples.primeNonzero base H) primePlan prime.setup.plan payload state false
    let rows := CompleteSimulation.primeRows prime (messagesFromSetup prime.circuit read.1 payload)
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
    native.claim = Current.Prime.Claim.fromRow (Current.Prime.batchRows rows.get
      (fun i => samples.prime (lookup samples.fallback future
        (state.rank.val+HonestTranscript.circuitFuel primePlan false)) i.val)) ∧
      native.eta = samples.primeNonzero (lookup samples.fallback future
        (state.rank.val+HonestTranscript.circuitFuel primePlan false+1)) := by
  let read := readSetup (CompleteTranscript.reader .prime (Equiv.refl P)
    samples.prime samples.primeNonzero base H) primePlan prime.setup.plan payload state false
  let batched := CompleteTranscript.step base H read.2
  have readRank : read.2.rank.val = state.rank.val+HonestTranscript.circuitFuel primePlan false := by
    rw [SimulationWrites.read_rank]
    exact Nat.min_eq_right (by omega)
  have batchInside : read.2.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by omega
  have batchRank : batched.2.rank.val = read.2.rank.val+1 := by
    rw [SimulationWrites.step_rank]
    exact Nat.min_eq_right (by omega)
  have scaleInside : batched.2.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by omega
  have batchFuture := (step_extends base H samples.fallback batched.2).trans extended
  have batchAnswer := step_answer_into base H samples.fallback read.2 future batchInside batchFuture
  have scaleAnswer := step_answer_into base H samples.fallback batched.2 future scaleInside extended
  rw [readRank] at batchAnswer
  rw [batchRank,readRank] at scaleAnswer
  change _ = _ ∧ samples.primeNonzero (CompleteTranscript.step base H batched.2).1 = _
  constructor
  · rw [← batchAnswer]
    rfl
  · rw [scaleAnswer]

omit [Fintype B] [DecidableEq B] in
theorem conversion_values
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C) (mu : P)
    (future : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (inside : native.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length)
    (extended : Extends samples.fallback
      (CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu).state future) :
    (CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu).alpha =
      samples.conversion (lookup samples.fallback future native.state.rank.val) := by
  let pending := CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }
  have answer := step_answer_into base H samples.fallback pending future inside extended
  exact congrArg samples.conversion answer

omit [DecidableEq B] in
theorem packing_values (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
      (simulateCircuit prime.circuit coins.prime)
    let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native coins.mu
    let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted coins.advice
      (simulateCircuit binary.description.template coins.binary)
    let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
    result.delta = (fun i => samples.binary (lookup samples.fallback result.state read.2.rank.val) i.val) := by
  let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
  let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
    (simulateCircuit prime.circuit coins.prime)
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native coins.mu
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted coins.advice
    (simulateCircuit binary.description.template coins.binary)
  let packing := Packing.simulate binary.basis 0 coins.packing
  let pending := CompleteTranscript.bind read.2 fun writes => { writes with packingU := some (fun i => (packing.1 i).val) }
  let packed := CompleteTranscript.step base H pending
  have finalRank := (SimulationWrites.simulate_properties binary prime primePlan samples base H context coins).1
  have inside : pending.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    by_contra outside
    have stopped : packed.2.rank.val = pending.rank.val := by
      simp only [packed,CompleteTranscript.step,dif_neg outside]
    have done : packed.2.rank.val = (CompleteSimulation.geometry binary prime primePlan).batchingIndex.val := finalRank
    have bound := (CompleteSimulation.geometry binary prime primePlan).batchingIndex.isLt
    omega
  have extended : Extends samples.fallback packed.2
      (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state :=
    bind_extends samples.fallback packed.2 _
  have answer := step_answer_into base H samples.fallback pending
    (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state inside extended
  funext i
  exact congrArg (fun value => samples.binary value i.val) answer

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationScalarAnswers
