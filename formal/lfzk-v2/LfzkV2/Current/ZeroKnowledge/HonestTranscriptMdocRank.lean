import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRank
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptOpening

/-! Static schedule alignment of the complete honest program. The packing
adapter has degree 128, so its one boundary is present. Both frontend budgets
are the lengths of their actual role lists; no fragment, scalar coordinate,
or shared input assertion contributes another boundary. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
open Merkle.RandomOracle SumcheckV2 ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {B Key Base C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "State" => CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C)
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)
local notation "Native" => CompleteSimulation.PrimePrefix binary prime primePlan Key Base C
local notation "Converted" => CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C
local notation "Result" => CompleteSimulation.RawResult binary prime primePlan Key Base C

omit [Fintype B] in
theorem native_counter (state : State) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → P) (pads : CircuitTape prime.circuit) (H : Point → Digest × C) :
    Counter (G).roles.length (fun state : State => state.rank.val) state
      ((native binary prime primePlan samples base state original remaining pads).run H).1.2.state
      (2+circuitFuel primePlan false) := by
  unfold native
  refine Counter.bind _ _ (fun read : CircuitResult P State (Fin prime.pads) prime.circuit => read.state)
    (fun read : Layered.Replay.Payload prime.circuit × Native => read.2.state) _ H
    (circuit_counter base .prime (Equiv.refl P) samples.prime samples.primeNonzero
      primePlan prime.setup.plan (CompleteHonest.primeInputs binary prime original remaining) 0 state pads false H) ?_
  intro read
  refine Counter.bind _ _ Prod.snd (fun read : Layered.Replay.Payload prime.circuit × Native => read.2.state) _ H
    (step_counter base read.state H) ?_
  intro batched
  rw [Tree.run_map]
  exact step_counter base batched.2 H

omit [Fintype B] in
theorem conversion_counter (native : Native) (mu : P) (H : Point → Digest × C) :
    Counter (G).roles.length (fun state : State => state.rank.val) native.state
      ((conversion binary prime primePlan samples base native mu).run H).1.state 1 := by
  simp only [conversion,Tree.run_map]
  exact (step_counter base
    (CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }) H).rebase rfl rfl

theorem binaryRead_counter (native : Native) (converted : Converted) (advice : MdocAdvice.Value)
    (inputs : Cube binary.input → B) (pads : CircuitTape binary.description.template) (H : Point → Digest × C) :
    Counter (G).roles.length (fun state : State => state.rank.val) converted.state
      ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).1.2.2
      (circuitFuel binary.plan false) := by
  simp only [binaryRead,Tree.run_map,retime_run]
  have counted := circuit_counter base .binary (Equiv.refl B) samples.binary samples.binaryNonzero
    (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
    (binary.description.setup _ _ _ _).plan inputs 0
    (CompleteSimulation.binaryStart binary prime primePlan converted advice)
    (CompleteShape.tapeEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) pads) false H
  simp only [CompleteSimulation.generatedPlan,circuitFuel_same] at counted
  exact counted.rebase rfl rfl

omit [Fintype B] in
theorem fuel_eq_batching : fuel binary prime primePlan = (G).batchingIndex.val := by
  unfold fuel
  rw [circuitFuel_roles binary.plan .binary,circuitFuel_roles primePlan .prime]
  simp only [Geometry.batchingIndex_val,Geometry.backendPrefix,CompleteSimulation.geometry,ConcreteSetup.geometry,
    List.length_append,List.length_cons,List.length_nil]
  have packing : binary.description.degree ≠ 1 := by change (128 : ℕ) ≠ 1; decide
  simp only [packing,↓reduceIte,List.length_cons,List.length_nil]
  omega

variable (coefficients : C →
  WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
variable (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
variable (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))

theorem program_counter (H : Point → Digest × C) :
    Counter (G).roles.length (fun state : State => state.rank.val)
      (CompleteTranscript.initial context samples.fallback)
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state
      (fuel binary prime primePlan) := by
  unfold program
  refine Counter.bind _ _ Prod.snd (fun result : Result => result.state) _ H
    (step_counter base (CompleteTranscript.initial context samples.fallback) H) ?_
  intro first
  dsimp only
  refine Counter.bind _ _ (fun read : Layered.Replay.Payload prime.circuit × Native => read.2.state)
    (fun result : Result => result.state) _ H ?_ ?_
  · exact (native_counter binary prime primePlan samples base
      (CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some (CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks) })
      original remaining tape.prime H).rebase rfl rfl
  intro primeRead
  try dsimp only
  refine Counter.bind _ _ (fun converted : Converted => converted.state) (fun result : Result => result.state) _ H ?_ ?_
  · exact conversion_counter binary prime primePlan samples base _ _ H
  intro converted
  try dsimp only
  refine Counter.bind _ _ (fun read : BinaryResult binary prime primePlan primeRead.2 converted _ => read.2.2)
    (fun result : Result => result.state) _ H ?_ ?_
  · exact binaryRead_counter binary prime primePlan samples base _ _ _ _ _ H
  intro read
  try dsimp only
  rw [Tree.run_map]
  exact (step_counter base
    (CompleteTranscript.bind read.2.2 fun writes => { writes with packingU := some (CompleteHonest.packingInstanceFromRead binary prime primePlan primeRead.2 converted
      (AdapterBits.xorEquiv
        (Adapter.Mdoc.advice primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original)
          primeRead.2.eta.val (fun _ => converted.alpha)
          (Adapter.Mdoc.offset primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original)
            primeRead.2.eta.val+tape.mask))
        (AdapterBits.rawOtpEquiv tape.otp).1) read.1 read.2.1 original tape).honestU }) H).rebase rfl rfl

theorem program_rank (H : Point → Digest × C) :
    ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state.rank.val =
      (G).batchingIndex.val := by
  have count := program_counter binary prime primePlan samples base coefficients context original remaining tape masks H
  simp only [Counter,CompleteTranscript.initial,Nat.zero_add,fuel_eq_batching] at count
  rw [Nat.min_eq_right (Nat.le_of_lt (G).batchingIndex.isLt)] at count
  exact count

theorem openingPrefix_rank
    (respond : Result → C → (Response G B × Response G P)) (H : Point → Digest × C) :
    ((openingPrefix binary prime primePlan samples base coefficients context original remaining tape masks respond).run H).1.state.rank.val =
      (G).openingIndex.val := by
  unfold openingPrefix
  rw [Tree.run_bind,Tree.run_map]
  have next := step_counter base
    ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state H
  simp only [Counter,program_rank] at next
  rw [← (G).openingIndex_val,Nat.min_eq_right (Nat.le_of_lt (G).openingIndex.isLt)] at next
  exact next

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
