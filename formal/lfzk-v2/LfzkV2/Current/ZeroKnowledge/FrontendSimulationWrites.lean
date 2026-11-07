import LfzkV2.Current.ZeroKnowledge.FrontendSimulationHistory
import LfzkV2.Current.ZeroKnowledge.FrontendWriteLog
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRank

/-! Public stage bookkeeping for the exact frontend write log. Query
counts depend only on the normalized public schedule. The log contains the
initial carried writes once and starts every subsequent boundary empty. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationWrites

open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section Readers
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F Pad : Type}
variable [Field F] (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

omit [Field F] in
theorem step_rank (state : CompleteTranscript.State g fields Advice Key Base C) :
    (CompleteTranscript.step base H state).2.rank.val = min g.roles.length (state.rank.val+1) := by
  have counted := HonestTranscript.step_counter base state H
  rw [HonestTranscript.step_output] at counted
  exact counted

theorem read_rank (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (payload : Layered.Replay.Payload body) (state : CompleteTranscript.State g fields Advice Key Base C)
    (continuing : Bool) :
    (readSetup (CompleteTranscript.reader side field decode nonzero base H)
      plan ids payload state continuing).2.rank.val =
        min g.roles.length (state.rank.val+HonestTranscript.circuitFuel plan continuing) := by
  rw [Prefix.circuit_state,HonestTranscript.execute_counter,HonestTranscript.circuit_length]

end Readers

variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
theorem capacity :
    (CompleteSimulation.geometry binary prime primePlan).roles.length =
      HonestTranscript.circuitFuel primePlan false+HonestTranscript.circuitFuel binary.plan false+7 := by
  have length := (CompleteSimulation.geometry binary prime primePlan).roles_length
  have packing : (CompleteSimulation.geometry binary prime primePlan).packingDegree ≠ 1 := by
    change (128:ℕ) ≠ 1
    decide
  rw [if_neg packing] at length
  rw [HonestTranscript.circuitFuel_roles primePlan .prime,
    HonestTranscript.circuitFuel_roles binary.plan .binary]
  change (CompleteSimulation.geometry binary prime primePlan).roles.length =
    (primePlan.frontend.roles .prime).length+(binary.plan.frontend.roles .binary).length+7
  change (CompleteSimulation.geometry binary prime primePlan).roles.length =
    (primePlan.frontend.roles .prime).length+(binary.plan.frontend.roles .binary).length+1+6 at length
  omega

def writes (coins : CompleteSimulation.Coins binary prime) :
    List (CompleteSimulation.Fresh binary prime primePlan) :=
  [WriteLog.empty] ++
    WriteLog.snapshots .prime (Equiv.refl P) { fingerprints := some coins.fingerprints }
      (Prefix.circuit primePlan (simulateCircuit prime.circuit coins.prime) false) ++
    [WriteLog.empty,WriteLog.empty,{ mu := some coins.mu }] ++
    WriteLog.snapshots .binary (Equiv.refl B) { advice := some coins.advice }
      (Prefix.circuit binary.plan (simulateCircuit binary.description.template coins.binary) false) ++
    [{ packingU := some (fun i => ((Packing.simulate binary.basis 0 coins.packing).1 i).val) }]

omit [Fintype B] [DecidableEq B] in
theorem selected_properties (context : Key) (fingerprints : Current.Fingerprints (MdocRuntime.fields B)) :
    let state := CompleteSimulation.selectedState binary prime primePlan samples base H context fingerprints
    state.rank.val = 1 ∧ WriteLog.log state = [WriteLog.empty] ∧
      state.pending = { fingerprints := some fingerprints } := by
  have inside : 0 < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    have length := (CompleteSimulation.geometry binary prime primePlan).roles_length
    omega
  simp only [CompleteSimulation.selectedState,
    CompleteTranscript.step_query base H (CompleteTranscript.initial context samples.fallback) inside]
  exact ⟨rfl,rfl,rfl⟩

omit [Fintype B] [DecidableEq B] in
theorem prime_properties
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (payload : Layered.Replay.Payload prime.circuit)
    (fits : state.rank.val+HonestTranscript.circuitFuel primePlan false+2 ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length) :
    let result := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
    result.state.rank.val = state.rank.val+HonestTranscript.circuitFuel primePlan false+2 ∧
      WriteLog.log result.state = WriteLog.log state ++
        WriteLog.snapshots .prime (Equiv.refl P) state.pending (Prefix.circuit primePlan payload false) ++
          [WriteLog.empty,WriteLog.empty] ∧
      result.state.pending = {} := by
  let read := readSetup
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan prime.setup.plan payload state false
  have readRank : read.2.rank.val = state.rank.val+HonestTranscript.circuitFuel primePlan false := by
    rw [read_rank]
    exact Nat.min_eq_right (by omega)
  have readFits : state.rank.val+(Prefix.circuit primePlan payload false).length ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [HonestTranscript.circuit_length]
    omega
  have readLog := WriteLog.circuit_log .prime (Equiv.refl P) base H samples.prime samples.primeNonzero
    primePlan prime.setup.plan payload false state readFits
  have readPending := WriteLog.circuit_pending .prime (Equiv.refl P) base H samples.prime samples.primeNonzero
    primePlan prime.setup.plan payload state readFits
  let batched := CompleteTranscript.step base H read.2
  have firstInside : read.2.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by omega
  have batchedRank : batched.2.rank.val = read.2.rank.val+1 := by
    rw [step_rank]
    exact Nat.min_eq_right (by omega)
  have secondInside : batched.2.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by omega
  have lastRank := step_rank base H batched.2
  have firstLog := WriteLog.step_log base H read.2 firstInside
  have secondLog := WriteLog.step_log base H batched.2 secondInside
  have firstPending := WriteLog.step_pending base H read.2 firstInside
  have secondPending := WriteLog.step_pending base H batched.2 secondInside
  change (CompleteTranscript.step base H batched.2).2.rank.val = _ ∧
    WriteLog.log (CompleteTranscript.step base H batched.2).2 = _ ∧
      (CompleteTranscript.step base H batched.2).2.pending = {}
  refine ⟨?_,?_,secondPending⟩
  · rw [lastRank,Nat.min_eq_right (by omega),batchedRank,readRank]
  · rw [secondLog,firstPending,firstLog,readPending,readLog]
    simp only [List.append_assoc,List.singleton_append,WriteLog.empty]

omit [Fintype B] [DecidableEq B] in
theorem conversion_properties
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C) (mu : P)
    (empty : native.state.pending = {})
    (fits : native.state.rank.val+1 ≤ (CompleteSimulation.geometry binary prime primePlan).roles.length) :
    let result := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu
    result.state.rank.val = native.state.rank.val+1 ∧
      WriteLog.log result.state = WriteLog.log native.state ++ [{ mu := some mu }] ∧
      result.state.pending = {} := by
  let pending := CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }
  have inside : pending.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    change native.state.rank.val < _
    omega
  have value : pending.pending = { mu := some mu } := by
    change { native.state.pending with mu := some mu } = _
    rw [empty]
  change (CompleteTranscript.step base H pending).2.rank.val = _ ∧
    WriteLog.log (CompleteTranscript.step base H pending).2 = _ ∧
      (CompleteTranscript.step base H pending).2.pending = {}
  refine ⟨?_,?_,WriteLog.step_pending base H pending inside⟩
  · rw [step_rank]
    exact Nat.min_eq_right fits
  · rw [WriteLog.step_log base H pending inside,value]
    rfl

omit [DecidableEq B] in
theorem binary_state
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template) :
    (CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload).2 =
      Prefix.execute .binary (Equiv.refl B) base H
        (CompleteSimulation.binaryStart binary prime primePlan converted advice)
        (Prefix.circuit binary.plan payload false) := by
  simp only [CompleteSimulation.binaryReplay,Prefix.circuit_state,CompleteSimulation.generatedPlan,
    Prefix.circuit_same]

omit [DecidableEq B] in
theorem binary_properties
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template)
    (empty : converted.state.pending = {})
    (fits : converted.state.rank.val+HonestTranscript.circuitFuel binary.plan false ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length) :
    let result := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload
    result.2.rank.val = converted.state.rank.val+HonestTranscript.circuitFuel binary.plan false ∧
      WriteLog.log result.2 = WriteLog.log converted.state ++
        WriteLog.snapshots .binary (Equiv.refl B) { advice := some advice }
          (Prefix.circuit binary.plan payload false) ∧ result.2.pending = {} := by
  let start := CompleteSimulation.binaryStart binary prime primePlan converted advice
  have startValue : start.pending = { advice := some advice } := by
    change { converted.state.pending with advice := some advice } = _
    rw [empty]
  have readFits : start.rank.val+(Prefix.circuit binary.plan payload false).length ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [HonestTranscript.circuit_length]
    exact fits
  dsimp only
  erw [binary_state]
  have fitsStart : start.rank.val+HonestTranscript.circuitFuel binary.plan false ≤
      (CompleteSimulation.geometry binary prime primePlan).roles.length := fits
  have rank := HonestTranscript.execute_counter base .binary (Equiv.refl B) start (Prefix.circuit binary.plan payload false) H
  rw [HonestTranscript.circuit_length,Nat.min_eq_right fitsStart] at rank
  have logged := WriteLog.execute_log .binary (Equiv.refl B) base H start _ readFits
  rw [startValue] at logged
  exact ⟨rank,logged,WriteLog.execute_pending .binary (Equiv.refl B) base H start _
    (WriteLog.circuit_nonempty binary.plan payload) readFits⟩

omit [DecidableEq B] in
theorem simulate_properties (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
    result.state.rank.val = (CompleteSimulation.geometry binary prime primePlan).batchingIndex.val ∧
      WriteLog.log result.state = writes binary prime primePlan coins ∧
      result.state.pending = { packingA := some (Packing.simulate binary.basis 0 coins.packing).2 } := by
  let selected := CompleteSimulation.selectedState binary prime primePlan samples base H context coins.fingerprints
  let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected
    (simulateCircuit prime.circuit coins.prime)
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native coins.mu
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted coins.advice
    (simulateCircuit binary.description.template coins.binary)
  let packing := Packing.simulate binary.basis 0 coins.packing
  let pending := CompleteTranscript.bind read.2 fun old => { old with packingU := some (fun i => (packing.1 i).val) }
  let packed := CompleteTranscript.step base H pending
  have cap := capacity binary prime primePlan
  have selectedFacts := selected_properties binary prime primePlan samples base H context coins.fingerprints
  have nativeFacts := prime_properties binary prime primePlan samples base H selected
    (simulateCircuit prime.circuit coins.prime) (by
      rw [selectedFacts.1,cap]
      omega)
  have convertedFacts := conversion_properties binary prime primePlan samples base H native coins.mu nativeFacts.2.2 (by
    rw [nativeFacts.1,selectedFacts.1,cap]
    omega)
  have binaryFacts := binary_properties binary prime primePlan samples base H native converted coins.advice
    (simulateCircuit binary.description.template coins.binary) convertedFacts.2.2 (by
      rw [convertedFacts.1,nativeFacts.1,selectedFacts.1,cap]
      omega)
  have readRank : read.2.rank.val =
      HonestTranscript.circuitFuel primePlan false+HonestTranscript.circuitFuel binary.plan false+4 := by
    rw [binaryFacts.1,convertedFacts.1,nativeFacts.1,selectedFacts.1]
    omega
  have inside : pending.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    change read.2.rank.val < _
    rw [readRank,cap]
    omega
  have pendingValue : pending.pending = { packingU := some (fun i => (packing.1 i).val) } := by
    change { read.2.pending with packingU := some (fun i => (packing.1 i).val) } = _
    rw [binaryFacts.2.2]
  have packedRank : packed.2.rank.val = read.2.rank.val+1 := by
    rw [step_rank]
    exact Nat.min_eq_right (by change read.2.rank.val+1 ≤ _; omega)
  have packedLog := WriteLog.step_log base H pending inside
  have packedPending := WriteLog.step_pending base H pending inside
  change packed.2.rank.val = _ ∧ WriteLog.log packed.2 = _ ∧
    { packed.2.pending with packingA := some packing.2 } = _
  refine ⟨?_,?_,?_⟩
  · rw [packedRank,readRank]
    have batch := (CompleteSimulation.geometry binary prime primePlan).batchingIndex_add_two
    omega
  · rw [packedLog,WriteLog.bind_log,pendingValue,binaryFacts.2.1,convertedFacts.2.1,
      nativeFacts.2.1,selectedFacts.2.1,selectedFacts.2.2]
    simp only [writes,List.append_assoc,List.cons_append]
    rfl
  · rw [packedPending]

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationWrites
