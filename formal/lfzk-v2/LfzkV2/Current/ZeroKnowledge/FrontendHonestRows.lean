import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling
import LfzkV2.Current.ZeroKnowledge.BackendStatement

/-! Honest completeness at the authenticated affine-statement boundary.
The ordinary circuit truth hypotheses imply the actual compiler rows at
the physical cell addresses. Fingerprints use those same cells, including
all later pads and the two dedicated masks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def fullPrimeRead (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → P) : Fin 768 ⊕ prime.Other → P :=
  Sum.elim (fun i => if WitnessInputs.shared binary original i then 1 else 0)
    (fun other => CompletePrimeCells.values remaining tape.mask
      (circuitPadValues prime.circuit tape.prime) selection (.inl other))

omit [Fintype B] [DecidableEq B] in
theorem fullPrimeRead_inputs (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → P) :
    circuitInputs prime.inputIndex prime.publicInputs (CellLayout.Prime.input 768 prime.remaining prime.pads)
      (fullPrimeRead binary prime original remaining tape selection) =
        CompleteHonest.primeInputs binary prime original remaining := by
  apply congrArg (zeroExtend prime.inputIndex)
  funext i
  cases i with
  | inl i => rfl
  | inr i => exact CompletePrimeCells.private_input_values remaining tape.mask _ selection _ i

omit [Fintype B] [DecidableEq B] in
theorem prime_rows
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → P)
    (valid : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining)) :
    let payload := realCircuit
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
    let read := readSetup
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan prime.setup.plan payload state false
    let messages := messagesFromSetup prime.circuit read.1 payload
    RowsHold (CompleteSimulation.primeRows prime messages) (fullPrimeRead binary prime original remaining tape selection) := by
  dsimp only
  have h := realCircuit_constraints
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan prime.setup.plan (CompleteHonest.primeInputs binary prime original remaining) valid state tape.prime
    (circuitPadValues prime.circuit tape.prime) (circuitPadValues_assignment prime.circuit tape.prime)
  obtain ⟨constraints,built,holds⟩ := h
  unfold CompleteSimulation.primeRows
  erw [built]
  apply (Linear.compile_correct _ _ _ _ _ _ _).mpr
  have inputs := fullPrimeRead_inputs binary prime original remaining tape selection
  let payload := realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
  let read := readSetup
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan prime.setup.plan payload state false
  let weights := prime.circuit.inputWeights (messagesFromSetup prime.circuit read.1 payload) 0
  have sumEq := input_sum prime.inputIndex weights prime.publicInputs (CellLayout.Prime.input 768 prime.remaining prime.pads)
    (fullPrimeRead binary prime original remaining tape selection)
  rw [inputs] at sumEq
  exact ⟨holds.1,holds.2.trans sumEq⟩

omit [Fintype B] [DecidableEq B] in
theorem prime_claim
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → P)
    (valid : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining)) :
    let payload := realCircuit
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
    native.claim.residual (fun i => if WitnessInputs.shared binary original i then 1 else 0)
      (fun other => CompletePrimeCells.values remaining tape.mask
        (circuitPadValues prime.circuit tape.prime) selection (.inl other)) = 0 := by
  have rows := prime_rows binary prime primePlan samples base H state original remaining tape selection valid
  dsimp only [CompleteSimulation.primePrefix]
  rw [Current.Prime.Claim.fromRow_residual,Current.Prime.batchRows_eval]
  apply Finset.sum_eq_zero
  intro i _
  exact mul_eq_zero_of_right _ (rows _ (List.get_mem _ _))

omit [Fintype B] [DecidableEq B] in
theorem prime_handoff
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → P)
    (valid : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining)) :
    let payload := realCircuit
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
    let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
    RowsHold [native.claim.row native.eta.val mu]
      (CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) selection) := by
  let payload := realCircuit
    (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
    primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
  let native := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
  have residual := prime_claim binary prime primePlan samples base H state original remaining tape selection valid
  change native.claim.residual (fun i => if WitnessInputs.shared binary original i then 1 else 0)
    (fun other => CompletePrimeCells.values remaining tape.mask
      (circuitPadValues prime.circuit tape.prime) selection (.inl other)) = 0 at residual
  change RowsHold [native.claim.row native.eta.val
    (Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask)] _
  intro row member
  rcases List.mem_singleton.mp member with rfl
  unfold CompletePrimeCells.values
  rw [Current.Prime.Claim.row_eval]
  dsimp only [Adapter.Mdoc.offset,Adapter.Mdoc.sharedSum,Current.Prime.Claim.residual,
    CompletePrimeCells.values,Sum.elim_inl] at residual ⊢
  linear_combination native.eta.val * residual

omit [DecidableEq B] in
theorem binary_fingerprints
    (coefficients : WitnessSelection.Coins B binary.description.Original)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) (masks : B × B) :
    RowsHold (FingerprintRows.rows
      (fun i => CellLayout.selected binary.description.cells (.inl i))
      (fun i => CellLayout.selected binary.description.cells (.inr i)) coefficients
      (WitnessSelection.fingerprint coefficients (CompleteHonest.binaryCandidate binary prime original tape masks)))
      (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks)) := by
  apply (FingerprintRows.rows_iff _ _ _ _ _).mpr
  rw [CompleteHonest.binaryCandidate_project]

omit [Fintype B] [DecidableEq B] in
theorem prime_project (remaining : Fin prime.remaining → P) (tape : CompleteHonest.Tape binary prime) (masks : P × P) :
    FingerprintRows.project
      (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
      (fun j => CellLayout.Prime.layout prime.remaining prime.pads (.inr j))
      (CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) ((finTwoArrowEquiv P).symm masks)) =
      CompleteHonest.primeCandidate binary prime remaining tape masks := by
  have projection := CompleteHonest.primeCandidate_project binary prime remaining tape masks
  have read : (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks)) ∘
      (CellLayout.Prime.index prime.remaining prime.pads) =
        CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) ((finTwoArrowEquiv P).symm masks) := by
    funext i
    exact CompletePrimeCells.flat_read _ _ _ _ i
  have data : ∀ i, (CellLayout.Prime.index prime.remaining prime.pads)
      (CellLayout.Prime.layout prime.remaining prime.pads i) = CellLayout.selected (CellLayout.Prime.cells prime.remaining prime.pads) i := by
    intro i
    exact (CellLayout.Prime.index prime.remaining prime.pads).apply_symm_apply _
  rw [← read]
  simpa only [FingerprintRows.project,Function.comp_def,data] using projection

omit [Fintype B] [DecidableEq B] in
theorem prime_fingerprints
    (coefficients : WitnessSelection.Coins P prime.Original)
    (remaining : Fin prime.remaining → P) (tape : CompleteHonest.Tape binary prime) (masks : P × P) :
    RowsHold (FingerprintRows.rows
      (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
      (fun j => CellLayout.Prime.layout prime.remaining prime.pads (.inr j)) coefficients
      (WitnessSelection.fingerprint coefficients (CompleteHonest.primeCandidate binary prime remaining tape masks)))
      (CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) ((finTwoArrowEquiv P).symm masks)) := by
  apply (FingerprintRows.rows_iff _ _ _ _ _).mpr
  rw [prime_project]

omit [Fintype B] [DecidableEq B] in
theorem prime_rows_selected
    (state : CompleteSimulation.State binary prime primePlan (Key := Key) (Base := Base) (C := C))
    (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : P × P)
    (coefficients : WitnessSelection.Coins P prime.Original)
    (valid : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining)) :
    let payload := realCircuit
      (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero base H)
      primePlan (CompleteHonest.primeInputs binary prime original remaining) 0 state tape.prime
    let native := CompleteSimulation.primePrefix binary prime primePlan samples base H state payload
    let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
    RowsHold ([native.claim.row native.eta.val mu] ++
      FingerprintRows.rows
        (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
        (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inr i)) coefficients
        (WitnessSelection.fingerprint coefficients (CompleteHonest.primeCandidate binary prime remaining tape masks)))
      (CompletePrimeCells.values remaining tape.mask (circuitPadValues prime.circuit tape.prime) ((finTwoArrowEquiv P).symm masks)) := by
  have front := prime_handoff binary prime primePlan samples base H state original remaining tape
    ((finTwoArrowEquiv P).symm masks) valid
  have selected := prime_fingerprints binary prime coefficients remaining tape masks
  dsimp only
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact front row member
  · exact selected row member

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows
