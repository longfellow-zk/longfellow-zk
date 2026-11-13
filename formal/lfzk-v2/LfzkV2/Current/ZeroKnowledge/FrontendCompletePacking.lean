import LfzkV2.Current.ZeroKnowledge.FrontendCorrectness
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest
import LfzkV2.Layered.PackedProver

/-! The binary sumcheck and the packing protocol share one physical pad
suffix. The circuit is fixed; the per-proof virtual definitions are
substituted into the final input equation, which is exactly the source
equation passed to the packing protocol. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompletePacking
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
omit [Fintype B] [DecidableEq B] in
theorem fieldBits_inputs (privateBits : Fin binary.nPrivate → Bool) :
    Current.Adapter.Circuit.bitValue (F := B) ∘ WitnessInputs.bits binary privateBits =
      circuitInputs binary.description.inputIndex
        (Current.Adapter.Circuit.bitValue ∘ binary.publicBits) id
        (Current.Adapter.Circuit.bitValue ∘ privateBits) := by
  change _ = circuitInputs
    (inputIndex binary.nPublic binary.nPrivate binary.input binary.committedCapacity) _ _ _
  funext q
  by_cases hp : (cubeIndex binary.input q).val < binary.nPublic
  · let i : Fin binary.nPublic := ⟨(cubeIndex binary.input q).val,hp⟩
    have hq : inputIndex binary.nPublic binary.nPrivate binary.input binary.committedCapacity (.inl i) = q := by
      apply (cubeIndex binary.input).injective
      apply Fin.ext
      exact inputIndex_public _ _ _ _ i
    rw [← hq,circuitInputs,zeroExtend_apply]
    simp only [Function.comp_apply,WitnessInputs.bits,inputIndex_public,dif_pos i.isLt]
    rfl
  · by_cases hv : (cubeIndex binary.input q).val-binary.nPublic < binary.nPrivate
    · let i : Fin binary.nPrivate := ⟨(cubeIndex binary.input q).val-binary.nPublic,hv⟩
      have hq : inputIndex binary.nPublic binary.nPrivate binary.input binary.committedCapacity (.inr i) = q := by
        apply (cubeIndex binary.input).injective
        apply Fin.ext
        have hi := inputIndex_private binary.nPublic binary.nPrivate binary.input binary.committedCapacity i
        change _ = (cubeIndex binary.input q).val
        rw [hi]
        dsimp only [i]
        omega
      rw [← hq,circuitInputs,zeroExtend_apply,Function.comp_apply]
      exact congrArg (Current.Adapter.Circuit.bitValue (F := B))
        (WitnessInputs.bits_private binary privateBits i)
    · have outside : ∀ i, inputIndex binary.nPublic binary.nPrivate binary.input binary.committedCapacity i ≠ q := by
        intro i eq
        have heq := congrArg (fun q => (cubeIndex binary.input q).val) eq
        cases i with
        | inl i => rw [inputIndex_public] at heq; exact hp (heq ▸ i.isLt)
        | inr i => rw [inputIndex_private] at heq; have := i.isLt; omega
      rw [circuitInputs,zeroExtend_outside _ _ _ outside]
      simp [Function.comp_apply,WitnessInputs.bits,hp,hv,Current.Adapter.Circuit.bitValue]

omit [Fintype B] [DecidableEq B] in
/-- The final input claim on the honest array is the substituted claim over
the public side and the committed bits. -/
theorem binaryInputs_dot (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) (weights : Cube binary.input → B) :
    dot weights (CompleteHonest.binaryInputs binary prime original tape entries) =
      dot (substitutedPublicWeights (fun i => weights (binary.description.inputIndex (.inl i)))
          (fun v => weights (binary.description.virtualIndex v)))
        (substitutedPublicInputs (Current.Adapter.Circuit.bitValue ∘ binary.description.publicBits) entries) +
      dot (substitutedPrivateWeights (fun i => weights (binary.description.inputIndex (.inr i)))
          (fun v => weights (binary.description.virtualIndex v)) entries)
        (fun i => if CompleteHonest.privateBits binary prime original tape i then 1 else 0) := by
  unfold CompleteHonest.binaryInputs CompleteHonest.arrayOf
  rw [virtual_input_sum]
  simp only [dot,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  rfl

omit [Fintype B] [DecidableEq B] in
theorem binaryPads_assignment (tape : CircuitTape binary.description.circuit) :
    Assignment binary.description.circuit binary.description.padPlan tape
      (CompleteHonest.binaryPads binary tape) := by
  apply assignment_of_values
  intro i
  change circuitPadValues binary.description.circuit tape
    (Fin.cast binary.description.circuit_pads.symm (Fin.cast binary.description.circuit_pads i)) = _
  congr 1

variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
/-- The compiler's affine equations hold on the physical sumcheck pad
suffix, including the derived product cell at each layer. -/
theorem binary_constraints
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B)
    (valid : binary.description.circuit.Satisfies inputs)
    (tape : CircuitTape binary.description.circuit) :
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      native converted advice inputs tape
    let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H converted advice payload
    let circuit := binary.description.circuit
    let messages := messagesFromSetup circuit read.1 payload
    let constraints := (Linear.buildConstraints (circuit.proof messages 0)).getD ⟨[],zeroClaim⟩
    constraints.Holds (CompleteHonest.binaryPads binary tape) (dot (circuit.inputWeights messages 0) inputs) := by
  dsimp only
  have h := realCircuit_constraints
    (CompleteTranscript.reader .binary (Equiv.refl B) samples.binary samples.binaryNonzero base H)
    binary.plan binary.description.padPlan inputs valid
    (CompleteSimulation.binaryStart binary prime primePlan converted advice) tape
    (CompleteHonest.binaryPads binary tape) (binaryPads_assignment binary tape)
  obtain ⟨constraints,built,holds⟩ := h
  exact Eq.mpr (congrArg (fun cs : Option (Linear.Constraints (Fin binary.description.pads) B) =>
    (cs.getD ⟨[],zeroClaim⟩).Holds (CompleteHonest.binaryPads binary tape) _) built) holds

omit [DecidableEq B] in
/-- A true binary circuit on the honest array, with this proof's virtual
definitions, supplies the packer's substituted source equality. -/
theorem packingInstance_valid
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (original : Fin binary.nPrivate → Bool)
    (tape : CompleteHonest.Tape binary prime)
    (valid : binary.description.circuit.Satisfies
      (CompleteHonest.binaryInputs binary prime original tape
        (CompleteSimulation.entries binary prime primePlan native converted advice))) :
    let inputs := CompleteHonest.binaryInputs binary prime original tape
      (CompleteSimulation.entries binary prime primePlan native converted advice)
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      native converted advice inputs tape.binary
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H
      native converted advice payload original tape
    inst.target = inst.trueValue := by
  dsimp only
  have h := binary_constraints binary prime primePlan samples base H native converted advice _ valid tape.binary
  have inputEquation := h.2.trans (binaryInputs_dot binary prime original tape _ _)
  dsimp only [CompleteHonest.packingInstance,CompleteHonest.packingInstanceFromRead,CompleteHonest.binaryCells]
  apply PackingCells.source_valid
  exact inputEquation

omit [DecidableEq B] in
/-- The honest packing instance varies only through its dedicated free
masks and r. The Frobenius cell is derived from that same r. -/
theorem packingInstance_change_coins
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.circuit)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime)
    (coins : Packing.Tape (F := B) (0 : Fin 128)) :
    CompleteHonest.packingInstance binary prime primePlan samples base H native converted advice payload
      original { tape with packing := coins } =
    Packing.honest (CompleteHonest.packingInstance binary prime primePlan samples base H
      native converted advice payload original tape) coins := by
  unfold CompleteHonest.packingInstance CompleteHonest.packingInstanceFromRead
  dsimp only [CompleteHonest.binaryCells,CompleteHonest.privateBits]
  have masks : PackingCells.freeMask (by decide : 0<128)
      ((PackingCells.freeMaskEquiv (by decide : 0<128)).symm coins.1) = coins.1 :=
    (PackingCells.freeMaskEquiv (by decide : 0<128)).apply_symm_apply coins.1
  refine (PackingCells.source_change_masks (by decide : 1<128) binary.description.capacity
    binary.basis _ _ _ _
    (CompleteHonest.privateBits binary prime original tape)
    ((PackingCells.freeMaskEquiv (by decide : 0<128)).symm tape.packing.1) tape.packing.2
    (CompleteHonest.binaryPads binary tape.binary) (0 : Fin 2 → B)
    ((PackingCells.freeMaskEquiv (by decide : 0<128)).symm coins.1) coins.2 (0 : Fin 2 → B)).trans ?_
  exact congrArg (Packing.honest _) (Prod.ext masks rfl)

end LfzkV2.Current.ZeroKnowledge.Frontend.CompletePacking
