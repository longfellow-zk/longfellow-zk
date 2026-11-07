import LfzkV2.Current.ZeroKnowledge.FrontendAdapterCorrectness
import LfzkV2.Current.ConcreteSetup

/-! Actual private mdoc addresses for the simulator's recovered adapter
cells. The scalar and quotient-pad suffix is constructed by arithmetic from
the checked input count; no injectivity or disjointness certificate is a
parameter. Original application bits before that suffix are preserved. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteInputs
open SumcheckV2
open ConcreteSetup
open scoped Classical
set_option maxRecDepth 2048
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

def privateValues (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin circuit.nPrivate) : Bool :=
  if hfirst : i.val < circuit.nPrivate-276 then original i
  else if hsecond : i.val < circuit.nPrivate-20 then
    mask ⟨i.val-(circuit.nPrivate-276),by have := circuit.privateCapacity; omega⟩
  else otp ⟨(i.val-(circuit.nPrivate-20))/10,by
      have := i.isLt; have := circuit.privateCapacity; omega⟩
    ⟨(i.val-(circuit.nPrivate-20))%10,Nat.mod_lt _ (by decide)⟩

theorem shared_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin 768) :
    privateValues circuit original mask otp (circuit.sharedPrivate i) = original (circuit.sharedPrivate i) := by
  exact dif_pos (circuit.shared_before_masks i)

theorem mask_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (i : Fin 256) :
    privateValues circuit original mask otp (circuit.maskPrivate i) = mask i := by
  have hc := circuit.privateCapacity
  have hi := i.isLt
  have hn : ¬(circuit.maskPrivate i).val < circuit.nPrivate-276 := by
    dsimp [BinaryCircuit.maskPrivate]; omega
  rw [privateValues,dif_neg hn,dif_pos (circuit.mask_before_advice i)]
  congr 1
  apply Fin.ext
  dsimp [BinaryCircuit.maskPrivate]
  omega

theorem otp_values (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool) (tree : Fin 2) (i : Fin 10) :
    privateValues circuit original mask otp (circuit.advicePrivate tree i) = otp tree i := by
  have hc := circuit.privateCapacity
  have hi := i.isLt
  have ht := tree.isLt
  have hn : ¬(circuit.advicePrivate tree i).val < circuit.nPrivate-276 := by
    dsimp [BinaryCircuit.advicePrivate]; omega
  have hm : ¬(circuit.advicePrivate tree i).val < circuit.nPrivate-20 := by
    dsimp [BinaryCircuit.advicePrivate]; omega
  rw [privateValues,dif_neg hn,dif_neg hm]
  congr 1
  · apply Fin.ext
    dsimp [BinaryCircuit.advicePrivate]
    have he : circuit.nPrivate-20+10*tree.val+i.val-(circuit.nPrivate-20) = 10*tree.val+i.val := by omega
    rw [he,Nat.add_comm (10*tree.val),Nat.add_mul_div_left _ _ (by decide : 0<10),Nat.div_eq_of_lt hi]
    omega
  · apply Fin.ext
    dsimp [BinaryCircuit.advicePrivate]
    have he : circuit.nPrivate-20+10*tree.val+i.val-(circuit.nPrivate-20) = 10*tree.val+i.val := by omega
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
    (ConcreteSetup.inputIndex circuit.nPublic circuit.nPrivate circuit.input circuit.inputCapacity (.inr i)) = _
  unfold bits
  rw [ConcreteSetup.inputIndex_private]
  have hn : ¬circuit.nPublic+i.val < circuit.nPublic := by omega
  simp only [dif_neg hn,Nat.add_sub_cancel_left,dif_pos i.isLt]

def shared (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool) : Fin 768 → Bool :=
  fun i => original (circuit.sharedPrivate i)

def recoveredPrivate (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) : Fin circuit.nPrivate → Bool :=
  privateValues circuit original
    (Adapter.canonicalMask Adapter.Mdoc.maskCapacity
      (Adapter.Mdoc.recoverMask weights (shared circuit original) eta mu))
    (MdocAdvice.bits ((AdapterBits.xorEquiv
      (Adapter.Mdoc.advice weights (shared circuit original) eta alpha mu)).symm masked))

theorem recovered_sources (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) :
    bits circuit (recoveredPrivate circuit original weights eta alpha mu masked) ∘ circuit.description.sources =
      Adapter.Mdoc.values weights (shared circuit original) eta mu := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply,ApplicationSetup.BinaryPublic.sources,Adapter.Mdoc.values,
      Handoff.values,Fin.addCases_left]
    change bits circuit _ (circuit.description.inputIndex (.inr (circuit.sharedPrivate j))) = _
    rw [bits_private]
    exact shared_values circuit original _ _ j
  · intro j
    simp only [Function.comp_apply,ApplicationSetup.BinaryPublic.sources,Adapter.Mdoc.values,
      Handoff.values,Fin.addCases_right]
    change bits circuit _ (circuit.description.inputIndex (.inr (circuit.maskPrivate j))) = _
    rw [bits_private]
    exact mask_values circuit original _ _ j

theorem recovered_otp (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) (tree : Fin 2) (i : Fin 10) :
    bits circuit (recoveredPrivate circuit original weights eta alpha mu masked) (circuit.description.advice tree i) =
      MdocAdvice.bits ((AdapterBits.xorEquiv
        (Adapter.Mdoc.advice weights (shared circuit original) eta alpha mu)).symm masked) tree i := by
  change bits circuit _ (circuit.description.inputIndex (.inr (circuit.advicePrivate tree i))) = _
  rw [bits_private]
  exact otp_values circuit original _ _ tree i

/-- The current physical source and OTP addresses, not an abstract copy of
them, make every generated adapter output zero on the recovered witness. -/
theorem recovered_adapter_satisfies [CharP B 2]
    (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool) (generator : Bˣ)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) :
    Current.Adapter.Circuit.Satisfies circuit.description.shape circuit.description.sources circuit.description.advice
      (fun tree i => generator^((alpha mu tree).val*Adapter.Mdoc.weights weights eta i).val)
      (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ))) (MdocAdvice.bits masked)
      (fun tree => generator^((alpha mu tree).val*mu).val)
      (Current.Adapter.Circuit.bitValue ∘
        bits circuit (recoveredPrivate circuit original weights eta alpha mu masked)) := by
  apply Adapter.product_check_satisfies
  intro tree
  have hs := recovered_sources circuit original weights eta alpha mu masked
  have ho := recovered_otp circuit original weights eta alpha mu masked
  simp only [BinaryCircuit.description] at hs ho ⊢
  rw [hs]
  simp_rw [ho]
  change Current.Adapter.ProductCheck generator (Adapter.Mdoc.weights weights eta)
    (Adapter.Mdoc.values weights (shared circuit original) eta mu) mu (alpha mu tree).val _
  unfold Adapter.Mdoc.advice
  rw [Adapter.recovered_advice]
  exact Adapter.honest_product_check generator _ _ _ _ (by decide) (Adapter.Mdoc.residual_zero _ _ _ _)

end LfzkV2.Current.ZeroKnowledge.Frontend.CompleteInputs
