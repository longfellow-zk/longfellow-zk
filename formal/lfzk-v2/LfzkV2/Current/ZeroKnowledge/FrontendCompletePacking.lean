import LfzkV2.Current.ZeroKnowledge.FrontendCorrectness
import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest
import LfzkV2.Layered.PackedProver

/-! The binary sumcheck and the packing protocol share one physical pad
suffix. Changing generated adapter coefficients changes neither these
addresses nor their values. The final sumcheck equation is exactly the
source equation passed to the packing protocol. -/
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
    Current.Adapter.Circuit.bitValue (F := B) ∘ CompleteInputs.bits binary privateBits =
      circuitInputs binary.description.inputIndex
        (Current.Adapter.Circuit.bitValue ∘ binary.publicBits) id
        (Current.Adapter.Circuit.bitValue ∘ privateBits) := by
  change _ = circuitInputs
    (inputIndex binary.nPublic binary.nPrivate binary.input binary.inputCapacity) _ _ _
  funext q
  by_cases hp : (cubeIndex binary.input q).val < binary.nPublic
  · let i : Fin binary.nPublic := ⟨(cubeIndex binary.input q).val,hp⟩
    have hq : inputIndex binary.nPublic binary.nPrivate binary.input binary.inputCapacity (.inl i) = q := by
      apply (cubeIndex binary.input).injective
      apply Fin.ext
      exact inputIndex_public _ _ _ _ i
    rw [← hq,circuitInputs,zeroExtend_apply]
    simp only [Function.comp_apply,CompleteInputs.bits,inputIndex_public,dif_pos i.isLt]
    rfl
  · by_cases hv : (cubeIndex binary.input q).val-binary.nPublic < binary.nPrivate
    · let i : Fin binary.nPrivate := ⟨(cubeIndex binary.input q).val-binary.nPublic,hv⟩
      have hq : inputIndex binary.nPublic binary.nPrivate binary.input binary.inputCapacity (.inr i) = q := by
        apply (cubeIndex binary.input).injective
        apply Fin.ext
        have hi := inputIndex_private binary.nPublic binary.nPrivate binary.input binary.inputCapacity i
        change _ = (cubeIndex binary.input q).val
        rw [hi]
        dsimp only [i]
        omega
      rw [← hq,circuitInputs,zeroExtend_apply,Function.comp_apply]
      exact congrArg (Current.Adapter.Circuit.bitValue (F := B))
        (CompleteInputs.bits_private binary privateBits i)
    · have outside : ∀ i, inputIndex binary.nPublic binary.nPrivate binary.input binary.inputCapacity i ≠ q := by
        intro i eq
        have heq := congrArg (fun q => (cubeIndex binary.input q).val) eq
        cases i with
        | inl i => rw [inputIndex_public] at heq; exact hp (heq ▸ i.isLt)
        | inr i => rw [inputIndex_private] at heq; have := i.isLt; omega
      rw [circuitInputs,zeroExtend_outside _ _ _ outside]
      simp [Function.comp_apply,CompleteInputs.bits,hp,hv,Current.Adapter.Circuit.bitValue]

omit [Fintype B] [DecidableEq B] in
theorem fieldBits_dot (privateBits : Fin binary.nPrivate → Bool) (weights : Cube binary.input → B) :
    dot weights (Current.Adapter.Circuit.bitValue ∘ CompleteInputs.bits binary privateBits) =
      dot (fun i => weights (binary.description.inputIndex (.inl i)))
        (Current.Adapter.Circuit.bitValue ∘ binary.publicBits) +
      dot (fun i => weights (binary.description.inputIndex (.inr i)))
        (fun i => if privateBits i then 1 else 0) := by
  rw [fieldBits_inputs,input_sum]
  simp only [dot,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Function.comp_apply,
    Function.id_def,Current.Adapter.Circuit.bitValue]
  rfl

omit [DecidableEq B] in
theorem binaryPads_assignment
    (powers : Fin 2 → Fin 1024 → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin 10 → Bool) (targets : Fin 2 → Bˣ)
    (tape : CircuitTape binary.description.template) :
    Assignment (binary.description.circuit powers base masked targets)
      (binary.description.setup powers base masked targets).plan
      (CompleteShape.tapeEquiv (binary.description.same_template powers base masked targets) tape)
      (CompleteHonest.binaryPads binary tape) := by
  apply assignment_of_values
  intro i
  let same := binary.description.same_template powers base masked targets
  have h := CompleteShape.tapeEquiv_padValues same tape
    (Fin.cast (CompleteShape.padCount same).symm i)
  have hc : Fin.cast (CompleteShape.padCount same)
      (Fin.cast (CompleteShape.padCount same).symm i) = i := by apply Fin.ext; rfl
  rw [hc] at h
  exact (congrArg (circuitPadValues binary.description.template tape)
    (show Fin.cast (binary.description.circuit_pads (fun _ _ => 1) 1 (fun _ _ => false) (fun _ => 1)).symm
        (Fin.cast (binary.description.circuit_pads powers base masked targets) i) =
      Fin.cast (CompleteShape.padCount same).symm i by apply Fin.ext; rfl)).trans h.symm

variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [DecidableEq B] in
/-- The compiler's affine equations hold on the physical sumcheck pad
suffix, including the derived product cell at each layer. -/
theorem binary_constraints
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (inputs : Cube binary.input → B)
    (valid : (CompleteSimulation.generatedCircuit binary prime primePlan native converted advice).Satisfies inputs)
    (tape : CircuitTape binary.description.template) :
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      native converted advice inputs tape
    let read := CompleteSimulation.binaryReplay binary prime primePlan samples base H native converted advice payload
    let circuit := CompleteSimulation.generatedCircuit binary prime primePlan native converted advice
    let messages := messagesFromSetup circuit read.1
      (CompleteShape.payloadEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) payload)
    let constraints := (Linear.buildConstraints (circuit.proof messages 0)).getD ⟨[],zeroClaim⟩
    constraints.Holds (CompleteHonest.binaryPads binary tape) (dot (circuit.inputWeights messages 0) inputs) := by
  dsimp only
  have h := realCircuit_constraints
    (CompleteTranscript.reader .binary (Equiv.refl B) samples.binary samples.binaryNonzero base H)
    (CompleteSimulation.generatedPlan binary prime primePlan native converted advice)
    (binary.description.setup _ _ _ _).plan inputs valid
    (CompleteSimulation.binaryStart binary prime primePlan converted advice)
    (CompleteShape.tapeEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted advice) tape)
    (CompleteHonest.binaryPads binary tape)
    (binaryPads_assignment binary _ _ _ _ tape)
  rw [← CompleteCoupling.binaryMessageEquiv_actual binary prime primePlan samples base H
    native converted advice inputs tape] at h
  obtain ⟨constraints,built,holds⟩ := h
  exact Eq.mpr (congrArg (fun cs : Option (Linear.Constraints (Fin binary.description.pads) B) =>
    (cs.getD ⟨[],zeroClaim⟩).Holds (CompleteHonest.binaryPads binary tape) _) built) holds

omit [DecidableEq B] in
/-- A true binary circuit supplies the packer's ordinary scalar source
equality. The packing coins do not enter this equality. -/
theorem packingInstance_valid
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (original : Fin binary.nPrivate → Bool)
    (tape : CompleteHonest.Tape binary prime)
    (valid : (CompleteSimulation.generatedCircuit binary prime primePlan native converted advice).Satisfies
      (Current.Adapter.Circuit.bitValue ∘ CompleteInputs.bits binary
        (CompleteHonest.privateBits binary prime original tape))) :
    let inputs := Current.Adapter.Circuit.bitValue (F := B) ∘
      CompleteInputs.bits binary (CompleteHonest.privateBits binary prime original tape)
    let payload := CompleteHonest.binaryMessageEquiv binary prime primePlan samples base H
      native converted advice inputs tape.binary
    let inst := CompleteHonest.packingInstance binary prime primePlan samples base H
      native converted advice payload original tape
    inst.target = inst.trueValue := by
  dsimp only
  have h := binary_constraints binary prime primePlan samples base H native converted advice _ valid tape.binary
  have inputEquation := h.2.trans (fieldBits_dot binary (CompleteHonest.privateBits binary prime original tape) _)
  dsimp only [CompleteHonest.packingInstance,CompleteHonest.packingInstanceFromRead,CompleteHonest.binaryCells]
  apply PackingCells.source_valid
  exact inputEquation

omit [DecidableEq B] in
/-- The honest packing instance varies only through its dedicated free
masks and r. The Frobenius cell is derived from that same r. -/
theorem packingInstance_change_coins
    (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (converted : CompleteSimulation.ConversionPrefix binary prime primePlan Key Base C)
    (advice : MdocAdvice.Value) (payload : Layered.Replay.Payload binary.description.template)
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
