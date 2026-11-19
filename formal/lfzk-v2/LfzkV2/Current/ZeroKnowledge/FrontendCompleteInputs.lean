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
    (MdocAdvice.bits ((AdapterBits.xorValue
      (Adapter.Mdoc.advice weights (shared circuit original) eta alpha mu)).symm masked))

theorem recovered_sources (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) :
    recoveredPrivate circuit original weights eta alpha mu masked ∘ circuit.description.sources =
      Adapter.Mdoc.values weights (shared circuit original) eta mu := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp only [Function.comp_apply,ApplicationSetup.BinaryPublic.sources,Adapter.Mdoc.values,
      Handoff.values,Fin.addCases_left]
    exact shared_values circuit original _ _ j
  · intro j
    simp only [Function.comp_apply,ApplicationSetup.BinaryPublic.sources,Adapter.Mdoc.values,
      Handoff.values,Fin.addCases_right]
    exact mask_values circuit original _ _ j

theorem recovered_otp (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) (tree : Fin 2) (i : Fin 10) :
    recoveredPrivate circuit original weights eta alpha mu masked (circuit.advicePrivate tree i) =
      MdocAdvice.bits ((AdapterBits.xorValue
        (Adapter.Mdoc.advice weights (shared circuit original) eta alpha mu)).symm masked) tree i :=
  otp_values circuit original _ _ tree i

/-- The current physical source and pad addresses, not an abstract copy of
them, make every tree's virtual leaves multiply to one on the recovered
witness. -/
theorem recovered_adapter_satisfies [CharP B 2]
    (circuit : BinaryCircuit B) (original : Fin circuit.nPrivate → Bool) (generator : Bˣ)
    (weights : Fin 768 → Adapter.Mdoc.P) (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas)
    (mu : Adapter.Mdoc.P) (masked : MdocAdvice.Value) (tree : Fin 2) :
    ∏ i, (Current.Adapter.Leaves.tree circuit.description.sources
      (fun j => generator^((alpha mu tree).val*Adapter.Mdoc.weights weights eta j).val)
      (circuit.advicePrivate tree) (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ)))
      (MdocAdvice.bits masked tree) (generator^((alpha mu tree).val*mu).val) i).value
        (Current.Adapter.Circuit.bitValue ∘ recoveredPrivate circuit original weights eta alpha mu masked) = 1 := by
  apply Adapter.product_check_leaves (by decide)
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
