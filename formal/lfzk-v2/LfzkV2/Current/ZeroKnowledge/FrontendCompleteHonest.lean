import LfzkV2.Current.ZeroKnowledge.FrontendCompletePrimeCells
import LfzkV2.Current.ZeroKnowledge.FrontendCompletePayload
import LfzkV2.Current.ZeroKnowledge.FrontendPackingCells

/-! Honest source coins and the complete frontend in the same staged
organization as the public simulator. Complete committed cells are fixed
before fingerprint challenges; in particular their construction receives
neither a reader, a transcript, nor a fingerprint response. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteHonest
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)

structure Tape (binary : BinaryCircuit B) (prime : PrimePublic P 768) where
  prime : CircuitTape prime.circuit
  mask : P
  otp : Fin (2^24)
  binary : CircuitTape binary.description.template
  packing : Packing.Tape (F := B) (0 : Fin 128)

abbrev Masks := Current.Fingerprints (CompleteSimulation.Fields (B := B))

def privateBits (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime) : Fin binary.nPrivate → Bool :=
  CompleteInputs.privateValues binary original (Adapter.canonicalMask Adapter.Mdoc.maskCapacity tape.mask)
    (fun tree i => tape.otp.val.testBit (10*tree.val+i.val))

def primeInputs (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P) : Cube prime.input → P :=
  circuitInputs prime.inputIndex prime.publicInputs id
    (Fin.addCases (fun i => if CompleteInputs.shared binary original i then 1 else 0) remaining)

def binaryPads (tape : CircuitTape binary.description.template) : Fin binary.description.pads → B :=
  circuitPadValues binary.description.template tape ∘
    Fin.cast (binary.description.circuit_pads (fun _ _ => 1) 1 (fun _ _ => false) (fun _ => 1)).symm

def binaryCells (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime) (selection : Fin 2 → B) :
    Fin (binary.description.cells+2) → B :=
  PackingCells.values (by decide : 0<128)
    (PackingCells.packedWords binary.basis (privateBits binary prime original tape))
    ((PackingCells.freeMaskEquiv (by decide : 0<128)).symm tape.packing.1)
    tape.packing.2 (binaryPads binary tape.binary) selection

def primeCells (remaining : Fin prime.remaining → P) (tape : Tape binary prime) (selection : Fin 2 → P) :
    Fin (CellLayout.Prime.cells prime.remaining prime.pads+2) → P :=
  CompletePrimeCells.flat remaining tape.mask (circuitPadValues prime.circuit tape.prime) selection

def binaryCandidate (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime) (masks : B × B) :
    WitnessSelection.Candidate B binary.description.Original :=
  (fun i => binaryCells binary prime original tape 0 (CellLayout.selected binary.description.cells (.inl i)),masks)

def primeCandidate (remaining : Fin prime.remaining → P) (tape : Tape binary prime) (masks : P × P) :
    WitnessSelection.Candidate P prime.Original :=
  (fun i => primeCells binary prime remaining tape 0
      (CellLayout.selected (CellLayout.Prime.cells prime.remaining prime.pads) (.inl i)),
    masks)

def responses
    (coefficients : WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P) (tape : Tape binary prime)
    (masks : Masks (B := B)) :
    Current.Fingerprints (CompleteSimulation.Fields (B := B)) :=
  (WitnessSelection.fingerprint (F := B) coefficients.1 (binaryCandidate binary prime original tape masks.1),
    WitnessSelection.fingerprint (F := P) coefficients.2 (primeCandidate binary prime remaining tape masks.2))

omit [DecidableEq B] in
theorem binaryCells_original (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime)
    (first second : Fin 2 → B) (i : binary.description.Original) :
    binaryCells binary prime original tape first (CellLayout.selected binary.description.cells (.inl i)) =
      binaryCells binary prime original tape second (CellLayout.selected binary.description.cells (.inl i)) := by
  change Fin.append _ first (Fin.castAdd 2 i) = Fin.append _ second (Fin.castAdd 2 i)
  rw [Fin.append_left,Fin.append_left]

omit [DecidableEq B] in
theorem binaryCandidate_project (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime)
    (masks : B × B) :
    FingerprintRows.project (fun i => CellLayout.selected binary.description.cells (.inl i))
      (fun i => CellLayout.selected binary.description.cells (.inr i))
      (binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks)) =
        binaryCandidate binary prime original tape masks := by
  apply Prod.ext
  · funext i
    exact binaryCells_original binary prime original tape _ _ i
  · apply Prod.ext <;> apply PackingCells.selection_value

omit [Fintype B] [DecidableEq B] in
theorem primeCandidate_project (remaining : Fin prime.remaining → P) (tape : Tape binary prime)
    (masks : P × P) :
    FingerprintRows.project (fun i => CellLayout.selected (CellLayout.Prime.cells prime.remaining prime.pads) (.inl i))
      (fun i => CellLayout.selected (CellLayout.Prime.cells prime.remaining prime.pads) (.inr i))
      (primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks)) =
        primeCandidate binary prime remaining tape masks := by
  apply Prod.ext
  · funext i
    exact CompletePrimeCells.flat_original _ _ _ _ _ i
  · apply Prod.ext
    · exact CompletePrimeCells.flat_selection remaining tape.mask _ _ 0
    · exact CompletePrimeCells.flat_selection remaining tape.mask _ _ 1

variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def binaryMessageEquiv
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B) :
    CircuitTape binary.description.template ≃ Layered.Replay.Payload binary.description.template :=
  CompleteCoupling.binaryMessageEquiv binary prime primePlan samples base H native converted advice inputs

def packingInstanceFromRead
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template)
    (setup : Layered.Circuit.Setup (Fin binary.description.pads)
      (CompleteSimulation.generatedCircuit binary prime primePlan native converted advice))
    (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime) :
    DualPacking.ArtinSchreier.Instance (ZMod 2) B (Fin 128) (Fin binary.description.words) :=
  let circuit := CompleteSimulation.generatedCircuit binary prime primePlan native converted advice
  let actualPayload := CompleteShape.payloadEquiv
    (CompleteSimulation.generatedSame binary prime primePlan native converted advice) payload
  let messages := messagesFromSetup circuit setup actualPayload
  let constraints := (Linear.buildConstraints (circuit.proof messages 0)).getD ⟨[],zeroClaim⟩
  let source := PackingCells.source (by decide : 1<128) binary.description.capacity binary.basis constraints.inputClaim
    (fun i => circuit.inputWeights messages 0 (binary.description.inputIndex (.inl i)))
    (Current.Adapter.Circuit.bitValue ∘ binary.publicBits)
    (fun i => circuit.inputWeights messages 0 (binary.description.inputIndex (.inr i)))
  source.realize (binaryCells binary prime original tape 0)

def packingInstance
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template)
    (original : Fin binary.nPrivate → Bool) (tape : Tape binary prime) :
    DualPacking.ArtinSchreier.Instance (ZMod 2) B (Fin 128) (Fin binary.description.words) :=
  packingInstanceFromRead binary prime primePlan native converted advice payload
    (CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload).1 original tape

def runSelected
    (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (fingerprints : Masks (B := B)) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : Tape binary prime) : CompleteSimulation.RawResult binary prime primePlan Key Base C :=
  let selected := CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some fingerprints }
  let primePayload := realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (primeInputs binary prime original remaining) 0 selected tape.prime
  let native := CompleteSimulation.primePrefix binary prime primePlan samples base H selected primePayload
  let mu := Adapter.Mdoc.offset native.claim.sharedWeights (CompleteInputs.shared binary original) native.eta.val+tape.mask
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu
  let alpha := fun _ : P => converted.alpha
  let quotient := Adapter.Mdoc.advice native.claim.sharedWeights (CompleteInputs.shared binary original) native.eta.val alpha mu
  let advice := AdapterBits.xorEquiv quotient (AdapterBits.rawOtpEquiv tape.otp).1
  let binaryPayload := binaryMessageEquiv binary prime primePlan samples base H native converted advice
    (Current.Adapter.Circuit.bitValue ∘ CompleteInputs.bits binary (privateBits binary prime original tape)) tape.binary
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice binaryPayload
  let inst := packingInstance binary prime primePlan samples base H native converted advice binaryPayload original tape
  let packingState := CompleteTranscript.bind read.2 fun writes => { writes with packingU := some inst.honestU }
  let packed := CompleteTranscript.step base H packingState
  let delta := fun i => samples.binary packed.1 i.val
  let a := inst.honestA delta
  let finished := CompleteTranscript.bind packed.2 fun writes => { writes with packingA := some a }
  { fingerprints := fingerprints
    primePayload := primePayload
    primeClaim := native.claim
    eta := native.eta
    mu := mu
    alpha := converted.alpha
    advice := advice
    binaryPayload := binaryPayload
    packing := (inst.honestU,a)
    delta := delta
    state := finished }

def run (coefficients : C →
      WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : Tape binary prime) (masks : Masks (B := B)) : CompleteSimulation.RawResult binary prime primePlan Key Base C :=
  let first := CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)
  let fingerprints := responses binary prime (coefficients first.1) original remaining tape masks
  runSelected binary prime primePlan samples base H first.2 fingerprints original remaining tape

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteHonest
