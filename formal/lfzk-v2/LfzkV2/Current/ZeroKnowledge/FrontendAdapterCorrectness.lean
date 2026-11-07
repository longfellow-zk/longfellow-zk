import LfzkV2.Current.ZeroKnowledge.FrontendAdapterMdoc
import LfzkV2.Current.AdapterCircuit

/-! The adapter simulator's recovered cells satisfy the generated product
checks. This closes the direction needed by honest frontend completeness;
the retained adapter extraction proof uses the converse direction. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Adapter
open SumcheckV2
open scoped Classical
variable {p d q : ℕ} [Fact p.Prime]

theorem honest_difference_zero (weights : Fin d → ZMod p) (values : Fin d → Bool)
    (target alpha : ZMod p) (hbits : d ≤ 2^q)
    (htrue : Current.Adapter.residual weights values target = 0) :
    Current.Adapter.difference weights values target alpha
      (honestQuotient weights values alpha hbits (by positivity)).val = 0 := by
  have h := honestQuotient_equation weights values target alpha hbits (by positivity) htrue
  have hi : (Current.Adapter.scaledSum weights values alpha : ℤ) =
      ((alpha*target).val : ℤ) +
        (honestQuotient weights values alpha hbits (by positivity)).val*p := by exact_mod_cast h
  unfold Current.Adapter.difference
  linarith

theorem honest_product_check {G : Type} [CommGroup G] (generator : G)
    (weights : Fin d → ZMod p) (values : Fin d → Bool) (target alpha : ZMod p)
    (hbits : d ≤ 2^q) (htrue : Current.Adapter.residual weights values target = 0) :
    Current.Adapter.ProductCheck generator weights values target alpha
      (honestQuotient weights values alpha hbits (by positivity)).val := by
  apply (Current.Adapter.product_check_iff generator rfl _ _ _ _ _).mpr
  rw [honest_difference_zero weights values target alpha hbits htrue]
  exact dvd_zero _

theorem recovered_advice (quotients : Fin 2 → Fin (2^10)) (masked : MdocAdvice.Value)
    (tree : Fin 2) :
    let otp := (AdapterBits.xorEquiv (AdapterBits.packedQuotients quotients)).symm masked
    Current.Adapter.Tree.binaryValue (List.ofFn fun i : Fin 10 =>
      Bool.xor (MdocAdvice.bits otp tree i) (MdocAdvice.bits masked tree i)) =
        (quotients tree).val := by
  dsimp only
  have heq : (fun i : Fin 10 => Bool.xor
      (MdocAdvice.bits ((AdapterBits.xorEquiv (AdapterBits.packedQuotients quotients)).symm masked) tree i)
      (MdocAdvice.bits masked tree i)) = fun i : Fin 10 => (quotients tree).val.testBit i.val := by
    funext i
    change Bool.xor ((masked.val ^^^ (AdapterBits.packedQuotients quotients).val).testBit
      (10*tree.val+i.val)) (masked.val.testBit (10*tree.val+i.val)) = _
    rw [Nat.testBit_xor]
    have h := AdapterBits.packedQuotients_bits quotients tree i
    simp only [MdocAdvice.bits] at h
    simpa only [Bool.xor_right_comm,Bool.xor_self,Bool.false_xor] using h
  rw [heq]
  exact AdapterBits.binaryValue_word (quotients tree)

theorem product_check_satisfies {B W : Type} [Field B] [CharP B 2] [Fintype W]
    (shape : Current.Adapter.Circuit.Shape d q) (sources : Fin d → W)
    (pads : Fin 2 → Fin q → W) (generator : Bˣ) (weights : Fin d → ZMod p)
    (target : ZMod p) (alpha : Fin 2 → ZMod p) (masked : Fin 2 → Fin q → Bool)
    (bits : W → Bool)
    (hproduct : ∀ tree, Current.Adapter.ProductCheck generator weights (bits ∘ sources)
      target (alpha tree) (Current.Adapter.Tree.binaryValue
        (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i)))) :
    Current.Adapter.Circuit.Satisfies shape sources pads
      (fun tree i => generator^(alpha tree*weights i).val) (generator^(-(p : ℤ))) masked
      (fun tree => generator^(alpha tree*target).val) (Current.Adapter.Circuit.bitValue ∘ bits) := by
  intro tree
  rw [Current.Adapter.Circuit.eval_products]
  have hq := Current.Adapter.Tree.quotientLeaves_prod (generator^(-(p : ℤ)))
    (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i))
  rw [Current.Adapter.Circuit.quotientLeaves_ofFn,List.prod_ofFn] at hq
  have hp := hproduct tree
  unfold Current.Adapter.ProductCheck at hp
  rw [← hq] at hp
  have hf := congrArg (fun x : Bˣ => (x : B)) hp
  simp only [Units.val_mul,Units.coe_prod,apply_ite,Units.val_one,Function.comp_apply] at hf
  rw [hf]
  exact CharTwo.add_self_eq_zero _

namespace Mdoc

/-- A shared input array for the generated adapter: the original 768 bits,
the canonical bits of the same recovered prime scalar, and the recovered
quotient OTP. Public source maps place these values in the application. -/
def recoveredInputs (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) (masked : MdocAdvice.Value) :
    Fin 1024 ⊕ (Fin 2 × Fin 10) → Bool :=
  Sum.elim (values sharedWeights shared eta mu) fun ⟨tree,i⟩ =>
    MdocAdvice.bits ((AdapterBits.xorEquiv (advice sharedWeights shared eta alpha mu)).symm masked) tree i

theorem recoveredInputs_satisfy {B : Type} [Field B] [CharP B 2]
    (shape : Current.Adapter.Circuit.Shape 1024 10) (generator : Bˣ)
    (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P) (alpha : Alphas)
    (mu : P) (masked : MdocAdvice.Value) :
    Current.Adapter.Circuit.Satisfies shape Sum.inl (fun tree i => Sum.inr (tree,i))
      (fun tree i => generator^((alpha mu tree).val*weights sharedWeights eta i).val)
      (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ))) (MdocAdvice.bits masked)
      (fun tree => generator^((alpha mu tree).val*mu).val)
      (Current.Adapter.Circuit.bitValue ∘ recoveredInputs sharedWeights shared eta alpha mu masked) := by
  apply product_check_satisfies
  intro tree
  change Current.Adapter.ProductCheck generator (weights sharedWeights eta)
    (values sharedWeights shared eta mu) mu (alpha mu tree).val _
  dsimp only [recoveredInputs,advice,Sum.elim_inr]
  rw [recovered_advice]
  exact honest_product_check generator _ _ _ _ (by decide) (residual_zero _ _ _ _)

end Mdoc
end LfzkV2.Current.ZeroKnowledge.Frontend.Adapter
