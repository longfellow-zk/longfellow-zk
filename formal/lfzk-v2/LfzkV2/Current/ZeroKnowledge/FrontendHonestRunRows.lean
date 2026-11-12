import LfzkV2.Current.ZeroKnowledge.FrontendHonestStatement

/-! Row truth for the actual honest frontend result. The helpers below
reconstruct the staged compiler inputs from its public messages, so the
canonical parser bridge can consume these rows without a satisfaction
certificate or a second computation of the honest circuit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.HonestRunRows
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def native (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (raw : CompleteSimulation.RawResult binary prime primePlan Key Base C) :=
  CompleteSimulation.primePrefix binary prime primePlan samples base H
    (CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some raw.fingerprints }) raw.primePayload

def converted (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (raw : CompleteSimulation.RawResult binary prime primePlan Key Base C) :=
  CompleteSimulation.conversionPrefix binary prime primePlan samples base H
    (native binary prime primePlan samples base H firstState raw) raw.mu

def binaryRows (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (coefficients : WitnessSelection.Coins B binary.description.Original)
    (raw : CompleteSimulation.RawResult binary prime primePlan Key Base C) :=
  HonestRows.binaryRows binary prime primePlan samples base H
    (native binary prime primePlan samples base H firstState raw)
    (converted binary prime primePlan samples base H firstState raw)
    raw.advice raw.binaryPayload raw.packing.1 raw.delta raw.packing.2 ++
      FingerprintRows.rows
        (fun i => CellLayout.selected binary.description.cells (.inl i))
        (fun i => CellLayout.selected binary.description.cells (.inr i)) coefficients raw.fingerprints.1

def primeRows (coefficients : WitnessSelection.Coins P prime.Original)
    (raw : CompleteSimulation.RawResult binary prime primePlan Key Base C) :=
  [raw.primeClaim.row raw.eta.val raw.mu] ++
    FingerprintRows.rows
      (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
      (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inr i)) coefficients raw.fingerprints.2

omit [DecidableEq B] in
set_option maxHeartbeats 800000 in
theorem selected_rows
    (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (coefficients : WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))
    (signature : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining))
    (hash :
      let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
      let raw := CompleteHonest.runSelected binary prime primePlan samples base H firstState responses original remaining tape
      HonestAdapter.hashChecks binary prime primePlan samples base H
        (native binary prime primePlan samples base H firstState raw) original tape) :
    let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
    let raw := CompleteHonest.runSelected binary prime primePlan samples base H firstState responses original remaining tape
    (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (raw.packing.1 i) = 0) ∧
      RowsHold (binaryRows binary prime primePlan samples base H firstState coefficients.1 raw)
        (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1)) ∧
      RowsHold (primeRows binary prime primePlan coefficients.2 raw)
        (BackendCells.primeRead (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2))) := by
  let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
  let raw := CompleteHonest.runSelected binary prime primePlan samples base H firstState responses original remaining tape
  let selected := CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some responses }
  let payload := realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 selected tape.prime
  let front := CompleteSimulation.primePrefix binary prime primePlan samples base H selected payload
  let mu := Adapter.Mdoc.offset front.claim.sharedWeights (WitnessInputs.shared binary original) front.eta.val+tape.mask
  let conversion := CompleteSimulation.conversionPrefix binary prime primePlan samples base H front mu
  let advice := HonestAdapter.advice binary prime primePlan samples base H front original tape
  let binaryPayload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H front conversion advice
    (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary (CompleteHonest.privateBits binary prime original tape)) tape.binary
  let inst := CompleteHonest.packingInstance binary prime primePlan samples base H front conversion advice binaryPayload original tape
  have stagedHash : HonestAdapter.hashChecks binary prime primePlan samples base H front original tape := hash
  have staged := HonestStatement.rows binary prime primePlan samples base H firstState coefficients original remaining
    tape masks raw.delta signature stagedHash
  have payloadEq : raw.primePayload = payload := rfl
  have fingerprintsEq : raw.fingerprints = responses := rfl
  have nativeEq : native binary prime primePlan samples base H firstState raw = front := by
    unfold native
    rw [payloadEq,fingerprintsEq]
  have muEq : raw.mu = mu := rfl
  have conversionEq : converted binary prime primePlan samples base H firstState raw = conversion := by
    unfold converted
    rw [nativeEq,muEq]
  have adviceEq : raw.advice = advice := by
    change AdapterBits.xorEquiv
      (Adapter.Mdoc.advice front.claim.sharedWeights (WitnessInputs.shared binary original) front.eta.val
        (fun _ => conversion.alpha) mu) (AdapterBits.rawOtpEquiv tape.otp).1 = _
    unfold advice HonestAdapter.advice
    rw [Adapter.Mdoc.advice_at]
    rfl
  have binaryPayloadEq : raw.binaryPayload = binaryPayload := by
    change CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H front conversion raw.advice
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary (CompleteHonest.privateBits binary prime original tape)) tape.binary = _
    rw [adviceEq]
  have uEq : raw.packing.1 = inst.honestU := by
    change (CompleteHonest.packingInstance binary prime primePlan samples base H front conversion raw.advice raw.binaryPayload
      original tape).honestU = _
    rw [adviceEq,binaryPayloadEq]
  have aEq : raw.packing.2 = inst.honestA raw.delta := by
    change (CompleteHonest.packingInstance binary prime primePlan samples base H front conversion raw.advice raw.binaryPayload
      original tape).honestA raw.delta = _
    rw [adviceEq,binaryPayloadEq]
  have claimEq : raw.primeClaim = front.claim := rfl
  have etaEq : raw.eta = front.eta := rfl
  change (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (raw.packing.1 i) = 0) ∧
    RowsHold (binaryRows binary prime primePlan samples base H firstState coefficients.1 raw) _ ∧
    RowsHold (primeRows binary prime primePlan coefficients.2 raw) _
  unfold binaryRows primeRows
  rw [nativeEq,conversionEq,adviceEq,binaryPayloadEq,uEq,aEq,claimEq,etaEq,muEq,fingerprintsEq]
  exact staged

omit [DecidableEq B] in
theorem run_rows
    (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))
    (signature : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining))
    (hash :
      let first := CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)
      let raw := CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks
      HonestAdapter.hashChecks binary prime primePlan samples base H
        (native binary prime primePlan samples base H first.2 raw) original tape) :
    let first := CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)
    let raw := CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks
    (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (raw.packing.1 i) = 0) ∧
      RowsHold (binaryRows binary prime primePlan samples base H first.2 (coefficients first.1).1 raw)
        (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1)) ∧
      RowsHold (primeRows binary prime primePlan (coefficients first.1).2 raw)
        (BackendCells.primeRead (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2))) := by
  let first := CompleteTranscript.step base H (CompleteTranscript.initial context samples.fallback)
  exact selected_rows binary prime primePlan samples base H first.2 (coefficients first.1)
    original remaining tape masks signature hash

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestRunRows
