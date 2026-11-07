import LfzkV2.Current.ZeroKnowledge.HonestTranscriptProgress
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest

/-! The complete honest mdoc frontend as one causal transcript program.
Private cells and pads are fixed before the first query. Every later scalar,
generated circuit and packing response is computed from the already returned
state and fixed private coins. There is no transcript oracle argument in the
program constructor; its output theorem identifies it with the existing
honest staged frontend. -/
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
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "State" => CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C)
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)
local notation "Native" => CompleteSimulation.PrimePrefix binary prime primePlan Key Base C
local notation "Converted" => CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C

def native (state : State) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (pads : CircuitTape prime.circuit) :
    Tree Point (Digest × C) (Layered.Replay.Payload prime.circuit × Native) (2+circuitFuel primePlan false) :=
  (circuit (complete base .prime (Equiv.refl P) samples.prime samples.primeNonzero)
    primePlan prime.setup.plan (CompleteHonest.primeInputs binary prime original remaining) 0 state pads false).bind
      fun read =>
        let rows := CompleteSimulation.primeRows prime (messagesFromSetup prime.circuit read.setup read.payload)
        (step base read.state).bind fun batched =>
          let claim := Current.Prime.Claim.fromRow (Current.Prime.batchRows rows.get
            (fun i => samples.prime batched.1 i.val))
          (step base batched.2).map fun rescaled =>
            (read.payload,⟨claim,samples.primeNonzero rescaled.1,rescaled.2⟩)

omit [Fintype B] [DecidableEq B] in
theorem native_output (state : State) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → P) (pads : CircuitTape prime.circuit) (H : Point → Digest × C) :
    ((native binary prime primePlan samples base state original remaining pads).run H).1 =
      let payload := realCircuit
        (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
        primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state pads
      (payload,CompleteSimulation.primePrefix binary prime primePlan samples base H state payload) := by
  have readEq := circuit_output
    (complete base .prime (Equiv.refl P) samples.prime samples.primeNonzero)
    primePlan prime.setup.plan (CompleteHonest.primeInputs binary prime original remaining) 0 state pads false H
  simp only [complete_reader] at readEq
  simp only [native,Tree.run_bind,Tree.run_map]
  rw [readEq]
  simp only [step_output]
  rfl

omit [Fintype B] [DecidableEq B] in
theorem native_progress (state : State) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → P) (pads : CircuitTape prime.circuit) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank state
      ((native binary prime primePlan samples base state original remaining pads).run H).1.2.state
      ((native binary prime primePlan samples base state original remaining pads).run H).2 := by
  simp only [native,Tree.run_bind,Tree.run_map]
  exact (circuit_progress _ _ _ (complete_progress base .prime (Equiv.refl P) samples.prime samples.primeNonzero)
    primePlan prime.setup.plan _ _ _ _ false H).trans
      ((step_progress base _ H).trans (step_progress base _ H))

def conversion (native : Native) (mu : P) : Tree Point (Digest × C) Converted 1 :=
  (step base (CompleteTranscript.bind native.state fun writes => { writes with mu := some mu })).map
    fun answer => ⟨mu,samples.conversion answer.1,answer.2⟩

omit [Fintype B] [DecidableEq B] in
theorem conversion_output (native : Native) (mu : P) (H : Point → Digest × C) :
    ((conversion binary prime primePlan samples base native mu).run H).1 =
      CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu := by
  simp only [conversion,Tree.run_map,step_output]
  rfl

omit [Fintype B] [DecidableEq B] in
theorem conversion_progress (native : Native) (mu : P) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank native.state
      ((conversion binary prime primePlan samples base native mu).run H).1.state
      ((conversion binary prime primePlan samples base native mu).run H).2 := by
  simp only [conversion,Tree.run_map]
  exact (step_progress base
    (CompleteTranscript.bind native.state fun writes => { writes with mu := some mu }) H).rebase rfl rfl

abbrev BinaryResult (native : Native) (converted : Converted) (advice : MdocAdvice.Value) :=
  Layered.Replay.Payload binary.description.template ×
    (Layered.Circuit.Setup (Fin binary.description.pads)
      (CompleteSimulation.generatedCircuit binary prime primePlan native converted advice) × State)

def binaryRead (native : Native) (converted : Converted) (advice : MdocAdvice.Value)
    (inputs : Cube binary.input → B) (pads : CircuitTape binary.description.template) :
    Tree Point (Digest × C) (BinaryResult binary prime primePlan native converted advice)
      (circuitFuel binary.plan false) :=
  let same := CompleteSimulation.generatedSame binary prime primePlan native converted advice
  let program := circuit (complete base .binary (Equiv.refl B) samples.binary samples.binaryNonzero)
    (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
    (binary.description.setup _ _ _ _).plan inputs 0
    (CompleteSimulation.binaryStart binary prime primePlan converted advice) (CompleteShape.tapeEquiv same pads) false
  (retime (circuitFuel_same same binary.plan false) program).map fun read =>
    ((CompleteShape.payloadEquiv same).symm read.payload,(read.setup,read.state))

omit [DecidableEq B] in
theorem binaryRead_output (native : Native) (converted : Converted) (advice : MdocAdvice.Value)
    (inputs : Cube binary.input → B) (pads : CircuitTape binary.description.template) (H : Point → Digest × C) :
    ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).1 =
      let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H native converted advice inputs pads
      (payload,CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload) := by
  have readEq := circuit_output (complete base .binary (Equiv.refl B) samples.binary samples.binaryNonzero)
    (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
    (binary.description.setup _ _ _ _).plan inputs 0
    (CompleteSimulation.binaryStart binary prime primePlan converted advice)
    (CompleteShape.tapeEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) pads) false H
  simp only [complete_reader] at readEq
  simp only [binaryRead,Tree.run_map,retime_run]
  rw [readEq]
  have actual := CompleteCoupling.binaryMessageEquiv_actual binary prime primePlan samples base H native converted advice inputs pads
  rw [← actual]
  rw [Equiv.symm_apply_apply]
  rfl

omit [DecidableEq B] in
theorem binaryRead_progress (native : Native) (converted : Converted) (advice : MdocAdvice.Value)
    (inputs : Cube binary.input → B) (pads : CircuitTape binary.description.template) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank converted.state
      ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).1.2.2
      ((binaryRead binary prime primePlan samples base native converted advice inputs pads).run H).2 := by
  simp only [binaryRead,Tree.run_map,retime_run]
  exact (circuit_progress _ _ _ (complete_progress base .binary (Equiv.refl B) samples.binary samples.binaryNonzero)
      (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
      (binary.description.setup _ _ _ _).plan inputs 0
      (CompleteSimulation.binaryStart binary prime primePlan converted advice)
      (CompleteShape.tapeEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) pads)
      false H).rebase rfl rfl

def fuel : ℕ := ((1+circuitFuel binary.plan false)+1)+(2+circuitFuel primePlan false)+1

def program (coefficients : C →
      WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) :
    Tree Point (Digest × C) (CompleteSimulation.RawResult binary prime primePlan Key Base C)
      (fuel binary prime primePlan) :=
  (step base (CompleteTranscript.initial context samples.fallback)).bind fun first =>
    let fingerprints := CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks
    let selected := CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some fingerprints }
    (native binary prime primePlan samples base selected original remaining tape.prime).bind fun primeRead =>
      let native := primeRead.2
      let mu := Adapter.Mdoc.offset native.claim.sharedWeights (CompleteInputs.shared binary original) native.eta.val+tape.mask
      (conversion binary prime primePlan samples base native mu).bind fun converted =>
        let quotient := Adapter.Mdoc.advice native.claim.sharedWeights (CompleteInputs.shared binary original)
          native.eta.val (fun _ => converted.alpha) mu
        let advice := AdapterBits.xorEquiv quotient (AdapterBits.rawOtpEquiv tape.otp).1
        (binaryRead binary prime primePlan samples base native converted advice
          (Current.Adapter.Circuit.bitValue ∘ CompleteInputs.bits binary (CompleteHonest.privateBits binary prime original tape))
          tape.binary).bind fun binaryRead =>
            let inst := CompleteHonest.packingInstanceFromRead binary prime primePlan native converted advice
              binaryRead.1 binaryRead.2.1 original tape
            let pending := CompleteTranscript.bind binaryRead.2.2 fun writes => { writes with packingU := some inst.honestU }
            (step base pending).map fun packed =>
              let delta := fun i => samples.binary packed.1 i.val
              let a := inst.honestA delta
              let finished := CompleteTranscript.bind packed.2 fun writes => { writes with packingA := some a }
              { fingerprints := fingerprints
                primePayload := primeRead.1
                primeClaim := native.claim
                eta := native.eta
                mu := mu
                alpha := converted.alpha
                advice := advice
                binaryPayload := binaryRead.1
                packing := (inst.honestU,a)
                delta := delta
                state := finished }


omit [DecidableEq B] in
theorem program_progress (coefficients : C →
      WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C) :
    RunProgress (fun state : State => state.rank.val) Input.rank
      (CompleteTranscript.initial context samples.fallback)
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).2 := by
  unfold program
  refine RunProgress.bind _ _ Prod.snd (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H
    (step_progress base (CompleteTranscript.initial context samples.fallback) H) ?_
  intro first
  try dsimp only
  refine RunProgress.bind _ _ (fun read : Layered.Replay.Payload prime.circuit × Native => read.2.state) (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact (native_progress binary prime primePlan samples base
      (CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some (CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks) })
      original remaining tape.prime H).rebase rfl rfl
  intro primeRead
  try dsimp only
  refine RunProgress.bind _ _ (fun converted : Converted => converted.state) (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact conversion_progress binary prime primePlan samples base _ _ H
  intro converted
  try dsimp only
  refine RunProgress.bind _ _ (fun read : BinaryResult binary prime primePlan primeRead.2 converted _ => read.2.2) (fun result : CompleteSimulation.RawResult binary prime primePlan Key Base C => result.state) _ H ?_ ?_
  · exact binaryRead_progress binary prime primePlan samples base _ _ _ _ _ H
  intro read
  try dsimp only
  rw [Tree.run_map]
  exact (step_progress base
    (CompleteTranscript.bind read.2.2 fun writes => { writes with packingU := some (CompleteHonest.packingInstanceFromRead binary prime primePlan primeRead.2 converted
        (AdapterBits.xorEquiv
          (Adapter.Mdoc.advice primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original)
            primeRead.2.eta.val (fun _ => converted.alpha)
            (Adapter.Mdoc.offset primeRead.2.claim.sharedWeights (CompleteInputs.shared binary original)
              primeRead.2.eta.val+tape.mask))
          (AdapterBits.rawOtpEquiv tape.otp).1) read.1 read.2.1 original tape).honestU }) H).rebase rfl rfl

omit [DecidableEq B] in
/-- The honest frontend is computed by the causal program, rather than by
making speculative calls to a transcript oracle. -/
theorem program_output (coefficients : C →
      WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C) :
    ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1 =
      CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks := by
  unfold program CompleteHonest.run CompleteHonest.runSelected
  rw [Tree.run_bind]
  rw [step_output]
  generalize hfirst : CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback) = first
  try dsimp only
  rw [Tree.run_bind]
  rw [native_output]
  try dsimp only
  generalize hpayload : realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (CompleteHonest.primeInputs binary prime original remaining) 0
    (CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some (CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks) }) tape.prime = primePayload
  generalize hnative : CompleteSimulation.primePrefix binary prime primePlan samples base H
    (CompleteTranscript.bind first.2 fun writes => { writes with fingerprints := some (CompleteHonest.responses binary prime (coefficients first.1) original remaining tape masks) }) primePayload = native
  try dsimp only
  rw [Tree.run_bind]
  rw [conversion_output]
  simp only [Adapter.Mdoc.advice]
  try dsimp only
  generalize hconverted : CompleteSimulation.conversionPrefix binary prime primePlan samples base H native
    (Adapter.Mdoc.offset native.claim.sharedWeights (CompleteInputs.shared binary original) native.eta.val+tape.mask) = converted
  try dsimp only
  rw [Tree.run_bind]
  rw [binaryRead_output]
  try dsimp only
  unfold CompleteHonest.packingInstance
  rw [Tree.run_map,step_output]

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
