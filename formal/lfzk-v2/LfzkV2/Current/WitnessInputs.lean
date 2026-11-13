import LfzkV2.Current.ConcreteSetup

/-! Physical input reconstruction shared by extraction and simulation. -/
noncomputable section
namespace LfzkV2.Current.WitnessInputs
open SumcheckV2 ConcreteSetup
open scoped Classical
set_option maxRecDepth 2048
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

def privateValues (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin circuit.nPrivate) : Bool :=
  if hfirst : i.val < circuit.hashPrivate then original i
  else if hsecond : i.val < (circuit.hashPrivate+256) then
    mask ⟨i.val-(circuit.hashPrivate),by have := circuit.hashCapacity; unfold BinaryCircuit.nPrivate at *; omega⟩
  else otp ⟨(i.val-((circuit.hashPrivate+256)))/10,by
      have := i.isLt; have := circuit.hashCapacity; unfold BinaryCircuit.nPrivate at *; omega⟩
    ⟨(i.val-((circuit.hashPrivate+256)))%10,Nat.mod_lt _ (by decide)⟩

theorem shared_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin 768) :
    privateValues circuit original mask otp (circuit.sharedPrivate i) = original (circuit.sharedPrivate i) := by
  exact dif_pos (circuit.shared_lt_hash i)

theorem mask_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin 256) :
    privateValues circuit original mask otp (circuit.maskPrivate i) = mask i := by
  have hc := circuit.hashCapacity
  have hi := i.isLt
  have hn : ¬(circuit.maskPrivate i).val < circuit.hashPrivate := by
    dsimp [BinaryCircuit.maskPrivate]; omega
  rw [privateValues,dif_neg hn,dif_pos (by dsimp [BinaryCircuit.maskPrivate]; omega)]
  congr 1
  apply Fin.ext
  dsimp [BinaryCircuit.maskPrivate]
  omega

theorem otp_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (tree : Fin 2) (i : Fin 10) :
    privateValues circuit original mask otp (circuit.advicePrivate tree i) = otp tree i := by
  have hc := circuit.hashCapacity
  have hi := i.isLt
  have ht := tree.isLt
  have hn : ¬(circuit.advicePrivate tree i).val < circuit.hashPrivate := by
    dsimp [BinaryCircuit.advicePrivate]; omega
  have hm : ¬(circuit.advicePrivate tree i).val < (circuit.hashPrivate+256) := by
    dsimp [BinaryCircuit.advicePrivate]; omega
  rw [privateValues,dif_neg hn,dif_neg hm]
  congr 1
  · apply Fin.ext
    dsimp [BinaryCircuit.advicePrivate]
    have he : (circuit.hashPrivate+256)+10*tree.val+i.val-((circuit.hashPrivate+256)) = 10*tree.val+i.val := by omega
    rw [he,Nat.add_comm (10*tree.val),Nat.add_mul_div_left _ _ (by decide : 0<10),Nat.div_eq_of_lt hi]
    omega
  · apply Fin.ext
    dsimp [BinaryCircuit.advicePrivate]
    have he : (circuit.hashPrivate+256)+10*tree.val+i.val-((circuit.hashPrivate+256)) = 10*tree.val+i.val := by omega
    rw [he,Nat.add_comm (10*tree.val),Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hi]

def bits (circuit : BinaryCircuit B) (privateBits : Fin circuit.nPrivate → Bool)
    (i : Cube circuit.input) : Bool :=
  let index := (ConcreteSetup.cubeIndex circuit.input i).val
  if hp : index < circuit.nPublic then circuit.publicBits ⟨index,hp⟩
  else if hv : index-circuit.nPublic < circuit.nPrivate then privateBits ⟨index-circuit.nPublic,hv⟩
  else false

theorem bits_private (circuit : BinaryCircuit B) (privateBits : Fin circuit.nPrivate → Bool)
    (i : Fin circuit.nPrivate) :
    bits circuit privateBits (circuit.description.inputIndex (.inr i)) = privateBits i := by
  change bits circuit privateBits
    (ConcreteSetup.inputIndex circuit.nPublic circuit.nPrivate circuit.input circuit.committedCapacity (.inr i)) = _
  unfold bits
  rw [ConcreteSetup.inputIndex_private]
  have hn : ¬circuit.nPublic+i.val < circuit.nPublic := by omega
  simp only [dif_neg hn,Nat.add_sub_cancel_left,dif_pos i.isLt]

def shared (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool) : Fin 768 → Bool :=
  fun i => original (circuit.sharedPrivate i)

theorem bits_public (circuit : BinaryCircuit B) (privateBits : Fin circuit.nPrivate → Bool)
    (i : Fin circuit.nPublic) :
    bits circuit privateBits (circuit.description.inputIndex (.inl i)) = circuit.publicBits i := by
  change bits circuit privateBits
    (ConcreteSetup.inputIndex circuit.nPublic circuit.nPrivate circuit.input circuit.committedCapacity (.inl i)) = _
  unfold bits
  rw [ConcreteSetup.inputIndex_public]
  exact dif_pos i.isLt

theorem bits_prefix (circuit : BinaryCircuit B) (first second : Fin circuit.nPrivate → Bool)
    (same : ∀ i, i.val < circuit.hashPrivate → first i = second i)
    (u : Cube circuit.input)
    (before : (cubeIndex circuit.input u).val < circuit.nPublic+(circuit.hashPrivate)) :
    bits circuit first u = bits circuit second u := by
  dsimp only [bits]
  split
  · rfl
  · split
    · apply same
      change (cubeIndex circuit.input u).val-circuit.nPublic < circuit.hashPrivate
      omega
    · rfl


end LfzkV2.Current.WitnessInputs
