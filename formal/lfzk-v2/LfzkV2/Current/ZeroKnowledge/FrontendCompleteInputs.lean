import LfzkV2.Current.WitnessInputs
import LfzkV2.Current.ZeroKnowledge.FrontendAdapterCorrectness
import LfzkV2.Current.ConcreteSetup

/-! Actual private mdoc addresses for the simulator's recovered adapter
cells. The scalar and quotient-pad suffix is constructed by arithmetic from
the checked input count; no injectivity or disjointness certificate is a
parameter. Original application bits before that suffix are preserved. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompleteInputs
open SumcheckV2
open ConcreteSetup WitnessInputs
open scoped Classical
set_option maxRecDepth 2048
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

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
