import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRecording
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdoc

/-! The actual honest frontend's emitted query keys are exactly the keys
saved in its final history, including both fields and the adapter/packing
boundaries. This is derived from the existing causal program constructors. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
open Merkle.RandomOracle SumcheckV2 ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit) (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "State" => CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C)
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)
local notation "Native" => CompleteSimulation.PrimePrefix binary prime primePlan Key Base C
local notation "Converted" => CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C

omit [Fintype B] [DecidableEq B] in
theorem native_recorded (state : State) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (pads : CircuitTape prime.circuit) (H : Point → Digest × C) :
    RunRecords queryLog state ((native binary prime primePlan samples base state original remaining pads).run H).1.2.state
      ((native binary prime primePlan samples base state original remaining pads).run H).2 := by
  simp only [native,Tree.run_bind,Tree.run_map]
  exact (circuit_recorded _ _ (complete_recorded base .prime (Equiv.refl P) samples.prime samples.primeNonzero)
    primePlan prime.setup.plan _ _ _ _ false H).trans
      ((step_recorded base _ H).trans (step_recorded base _ H))

omit [Fintype B] [DecidableEq B] in
theorem conversion_recorded (native : Native) (mu : P) (H : Point → Digest × C) :
    RunRecords queryLog native.state ((conversion binary prime primePlan samples base native mu).run H).1.state
      ((conversion binary prime primePlan samples base native mu).run H).2 := by
  simp only [conversion,Tree.run_map]
  exact (step_recorded base (CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }) H).rebase rfl rfl

omit [DecidableEq B] in
theorem binaryRead_recorded (native : Native) (converted : Converted) (advice : MdocAdvice.Value)
    (inputs : Cube binary.input → B) (pads : CircuitTape binary.description.template) (H : Point → Digest × C) :
    RunRecords queryLog converted.state
      ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).1.2.2
      ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).2 := by
  simp only [binaryRead,Tree.run_map,retime_run]
  exact (circuit_recorded _ _ (complete_recorded base .binary (Equiv.refl B) samples.binary samples.binaryNonzero)
    (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
    (binary.description.setup _ _ _ _).plan inputs 0 (CompleteSimulation.binaryStart binary prime primePlan converted advice)
    (CompleteShape.tapeEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) pads) false H).rebase rfl rfl

omit [DecidableEq B] in
theorem program_recorded (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C) :
    RunRecords queryLog (CompleteTranscript.initial context samples.fallback)
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).2 := by
  unfold program
  refine RunRecords.bind queryLog _ _ Prod.snd (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H
    (step_recorded base (CompleteTranscript.initial context samples.fallback) H) ?_
  intro first
  try dsimp only
  refine RunRecords.bind queryLog _ _ (fun read : Layered.Replay.Payload prime.circuit × Native => read.2.state)
    (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact (native_recorded binary prime primePlan samples base
      (CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some (CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks) })
      original remaining tape.prime H).rebase rfl rfl
  intro primeRead
  try dsimp only
  refine RunRecords.bind queryLog _ _ (fun converted : Converted => converted.state)
    (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact conversion_recorded binary prime primePlan samples base _ _ H
  intro converted
  try dsimp only
  refine RunRecords.bind queryLog _ _ (fun read : BinaryResult binary prime primePlan primeRead.2 converted _ => read.2.2)
    (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact binaryRead_recorded binary prime primePlan samples base _ _ _ _ _ H
  intro read
  try dsimp only
  rw [Tree.run_map]
  exact (step_recorded base
    (CompleteTranscript.bind read.2.2 fun writes => { writes with packingU := some (CompleteHonest.packingInstanceFromRead binary prime primePlan primeRead.2 converted
      (AdapterBits.xorEquiv (Adapter.Mdoc.advice primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original)
        primeRead.2.eta.val (fun _ => converted.alpha)
        (Adapter.Mdoc.offset primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original) primeRead.2.eta.val+tape.mask))
        (AdapterBits.rawOtpEquiv tape.otp).1) read.1 read.2.1 original tape).honestU }) H).rebase rfl rfl

omit [DecidableEq B] in
/-- Every key in the actual trace is an earlier key of the returned state,
with its full cached physical prefix retained. -/
theorem program_query_mem (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C)
    (qa : Point × (Digest × C))
    (member : qa ∈ ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).2) :
    qa.1 ∈ queryLog (CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks).state := by
  have record := program_recorded binary prime primePlan samples base coefficients context original remaining tape masks H
  have recorded := record.mem qa member
  rw [program_output] at recorded
  exact recorded

omit [DecidableEq B] in
/-- Changing answers outside the actual returned history leaves the whole
honest execution unchanged, including its ordered trace. -/
theorem program_congr_queryLog (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H H' : Point → Digest × C)
    (agree : ∀ point ∈ queryLog (CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks).state,
      H' point = H point) :
    (program binary prime primePlan samples base coefficients context original remaining tape masks).run H' =
      (program binary prime primePlan samples base coefficients context original remaining tape masks).run H := by
  apply Tree.run_congr_on_trace
  intro qa member
  exact (agree qa.1 (program_query_mem binary prime primePlan samples base coefficients context original remaining tape masks H qa member)).trans
    ((program binary prime primePlan samples base coefficients context original remaining tape masks).trace_sound H qa member).symm

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
