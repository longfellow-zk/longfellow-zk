import LfzkV2.Current.ZeroKnowledge.FrontendHonestRows

/-! The binary frontend's actual terminal rows and two packing rows are
true on its complete physical witness vector. The final input equation is
compiled with this proof's virtual definitions substituted. The dedicated
fingerprint masks are retained in that vector and absent from these frontend
equations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows
open SumcheckV2 ApplicationSetup ConcreteSetup DualPacking.ArtinSchreier
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)

omit [DecidableEq B] in
theorem binary_inputs (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime)
    (selection : Fin 2 → B) (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) :
    binary.description.inputs entries (CompleteHonest.binaryCells binary prime original tape selection) =
      CompleteHonest.binaryInputs binary prime original tape entries := by
  unfold BinaryPublic.inputs Packed.Statement.virtualInputs CompleteHonest.binaryInputs CompleteHonest.arrayOf
  congr 1
  funext i
  exact PackingCells.unpack_values (by decide : 0<128) binary.description.capacity binary.basis
    (CompleteHonest.privateBits binary prime original tape)
    ((PackingCells.freeMaskEquiv (by decide : 0<128)).symm tape.packing.1) tape.packing.2
    (CompleteHonest.binaryPads binary tape.binary) selection i

variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def binaryRows
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.circuit)
    (U delta : Fin 128 → B) (A : B) : List (LinearRow binary.description.Slot B) :=
  let circuit := binary.description.circuit
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H converted advice payload
  let messages := messagesFromSetup circuit read.1 payload
  let constraints := (Linear.buildConstraints (circuit.proof messages 0)).getD ⟨[],zeroClaim⟩
  Layered.Packed.virtualRows binary.description.packing constraints (circuit.inputWeights messages 0)
    binary.description.inputIndex binary.description.virtualIndex binary.description.packedIndex
    (CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
    (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits)
    (CompleteSimulation.entries binary prime primePlan native converted advice) U delta A

omit [DecidableEq B] in
theorem binary_rows
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (original : Fin binary.nPrivate → Bool)
    (tape : CompleteHonest.Tape binary prime) (selection : Fin 2 → B) (delta : Fin 128 → B)
    (valid : binary.description.circuit.Satisfies
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan native converted advice))) :
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H native converted advice
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan native converted advice)) tape.binary
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H native converted advice payload original tape
    (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (inst.honestU i) = 0) ∧
      RowsHold (binaryRows binary prime primePlan samples base H native converted advice payload inst.honestU delta (inst.honestA delta))
        (CompleteHonest.binaryCells binary prime original tape selection) := by
  dsimp only
  have holds := CompletePacking.binary_constraints binary prime primePlan samples base H native converted advice _ valid tape.binary
  unfold binaryRows
  let entries := CompleteSimulation.entries binary prime primePlan native converted advice
  let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H native converted advice
    (CompleteHonest.binaryInputs binary prime original tape entries) tape.binary
  let circuit := binary.description.circuit
  let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H converted advice payload
  let messages := messagesFromSetup circuit read.1 payload
  let constraints := (Linear.buildConstraints (circuit.proof messages 0)).getD ⟨[],zeroClaim⟩
  have hpad : CompleteHonest.binaryCells binary prime original tape selection ∘
      CellLayout.Binary.pad binary.description.words 128 binary.description.pads = CompleteHonest.binaryPads binary tape.binary := by
    funext i
    exact PackingCells.pad_value _ _ _ _ _ _ i
  have hinput := binary_inputs binary prime original tape selection entries
  have hholds : constraints.Holds (CompleteHonest.binaryCells binary prime original tape selection ∘
      CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
      (dot (circuit.inputWeights messages 0) (binary.description.packing.virtualInputs binary.description.inputIndex
        binary.description.virtualIndex binary.description.packedIndex
        (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits) entries
        (CompleteHonest.binaryCells binary prime original tape selection))) := by
    change constraints.Holds _ (dot _ (binary.description.inputs entries _))
    rw [hpad,hinput]
    exact holds
  have hmask : frobenius (ZMod 2) B
      (binary.description.packing.realize (CompleteHonest.binaryCells binary prime original tape selection)).r =
      (binary.description.packing.realize (CompleteHonest.binaryCells binary prime original tape selection)).b := by
    exact (congrArg (frobenius (ZMod 2) B) (PackingCells.random_value _ _ _ _ _ _)).trans
      (PackingCells.frobenius_value _ _ _ _ _ _).symm
  have complete := Layered.Packed.honest_virtual_rows binary.description.packing constraints
    (circuit.inputWeights messages 0) binary.description.inputIndex binary.description.virtualIndex
    binary.description.packedIndex (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits) entries
    (CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
    (CompleteHonest.binaryCells binary prime original tape selection) hholds delta hmask
  have instance_eq :
      ((binary.description.packing.withVirtualSource binary.description.packedIndex constraints.inputClaim
        (CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
        (circuit.inputWeights messages 0) binary.description.inputIndex binary.description.virtualIndex
        (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits) entries).realize
          (CompleteHonest.binaryCells binary prime original tape selection)) =
        CompleteHonest.packingInstance binary prime primePlan samples base H native converted advice payload original tape := by
    unfold CompleteHonest.packingInstance CompleteHonest.packingInstanceFromRead CompleteHonest.binaryCells
    erw [PackingCells.source_realize,PackingCells.source_realize]
    rfl
  exact Eq.mp (congrArg (fun inst =>
    (∀ i, DualPacking.ArtinSchreier.traceF (ZMod 2) (inst.honestU i) = 0) ∧
      RowsHold (Layered.Packed.virtualRows binary.description.packing constraints (circuit.inputWeights messages 0)
        binary.description.inputIndex binary.description.virtualIndex binary.description.packedIndex
        (CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
        (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits) entries inst.honestU delta (inst.honestA delta))
        (CompleteHonest.binaryCells binary prime original tape selection)) instance_eq) complete

omit [DecidableEq B] in
theorem binary_rows_selected
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (original : Fin binary.nPrivate → Bool)
    (tape : CompleteHonest.Tape binary prime) (masks : B × B) (delta : Fin 128 → B)
    (coefficients : WitnessSelection.Coins B binary.description.Original)
    (valid : binary.description.circuit.Satisfies
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan native converted advice))) :
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H native converted advice
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan native converted advice)) tape.binary
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H native converted advice payload original tape
    RowsHold (binaryRows binary prime primePlan samples base H native converted advice payload inst.honestU delta (inst.honestA delta) ++
      FingerprintRows.rows
        (fun i => CellLayout.selected binary.description.cells (.inl i))
        (fun i => CellLayout.selected binary.description.cells (.inr i)) coefficients
        (WitnessSelection.fingerprint coefficients (CompleteHonest.binaryCandidate binary prime original tape masks)))
      (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks)) := by
  have front := (binary_rows binary prime primePlan samples base H native converted advice original tape
    ((finTwoArrowEquiv B).symm masks) delta valid).2
  have selected := binary_fingerprints binary prime coefficients original tape masks
  dsimp only
  intro row member
  rcases List.mem_append.mp member with member | member
  · exact front row member
  · exact selected row member

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows
