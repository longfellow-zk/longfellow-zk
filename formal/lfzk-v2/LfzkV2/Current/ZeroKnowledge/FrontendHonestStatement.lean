import LfzkV2.Current.ZeroKnowledge.FrontendHonestAdapter

/-! The staged honest frontend supplies both exact affine row lists later
authenticated by the joint backend. Every cell, including the dedicated
fingerprint masks, is read from the actual physical layout. No backend
satisfaction premise is supplied to this construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.HonestStatement
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
theorem prime_cells_read (remaining : Fin prime.remaining → P) (tape : CompleteHonest.Tape binary prime)
    (selection : Fin 2 → P) :
    BackendCells.primeRead (CompleteHonest.primeCells binary prime remaining tape selection) =
      CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) selection := by
  funext i
  exact CompletePrimeCells.flat_read _ _ _ _ i

omit [DecidableEq B] in
theorem rows
    (firstState : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (coefficients : WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (delta : Fin 128 → B)
    (signature : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining))
    (hash :
      let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
      let selected := CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some responses }
      let payload := realCircuit
        (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
        primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 selected tape.prime
      HonestAdapter.hashChecks binary prime primePlan samples base H
        (CompleteSimulation.primePrefix binary prime primePlan samples base H selected payload) original tape) :
    let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
    let selected := CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some responses }
    let primePayload := realCircuit
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 selected tape.prime
    let front := CompleteSimulation.primePrefix binary prime primePlan samples base H selected primePayload
    let mu := Adapter.Mdoc.offset front.claim.sharedWeights (WitnessInputs.shared binary original) front.eta.val+tape.mask
    let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H front mu
    let advice := HonestAdapter.advice binary prime primePlan samples base H front original tape
    let binaryPayload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H front converted advice
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan front converted advice)) tape.binary
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H front converted advice binaryPayload original tape
    (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (inst.honestU i) = 0) ∧
      RowsHold (HonestRows.binaryRows binary prime primePlan samples base H front converted advice binaryPayload
          inst.honestU delta (inst.honestA delta) ++
        FingerprintRows.rows
          (fun i => CellLayout.selected binary.description.cells (.inl i))
          (fun i => CellLayout.selected binary.description.cells (.inr i)) coefficients.1 responses.1)
        (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1)) ∧
      RowsHold (front.claim.rows front.eta.val mu ++
        FingerprintRows.rows
          (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
          (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inr i)) coefficients.2 responses.2)
        (BackendCells.primeRead (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2))) := by
  let responses := CompleteHonest.responses binary prime coefficients original remaining tape masks
  let selected := CompleteTranscript.bind firstState fun writes => { writes with fingerprints := some responses }
  let payload := realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 selected tape.prime
  let front := CompleteSimulation.primePrefix binary prime primePlan samples base H selected payload
  let mu := Adapter.Mdoc.offset front.claim.sharedWeights (WitnessInputs.shared binary original) front.eta.val+tape.mask
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H front mu
  let advice := HonestAdapter.advice binary prime primePlan samples base H front original tape
  have valid := HonestAdapter.generated_satisfies binary prime primePlan samples base H front original tape hash
  have trace := (HonestRows.binary_rows binary prime primePlan samples base H front converted advice original tape
    ((finTwoArrowEquiv B).symm masks.1) delta valid).1
  have binaryRows := HonestRows.binary_rows_selected binary prime primePlan samples base H front converted advice original tape
    masks.1 delta coefficients.1 valid
  have primeRows := HonestRows.prime_rows_selected binary prime primePlan samples base H selected original remaining tape masks.2
    coefficients.2 signature
  exact ⟨trace,binaryRows,Eq.mpr (congrArg (RowsHold _) (prime_cells_read binary prime remaining tape _)) primeRows⟩

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestStatement
