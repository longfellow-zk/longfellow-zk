import LfzkV2.Current.ZeroKnowledge.FrontendAdapterMdoc
import LfzkV2.Current.AdapterLeaves

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

theorem recovered_advice (quotients masked : MdocAdvice.Value) (tree : Fin 2) :
    let otp := (AdapterBits.xorValue quotients).symm masked
    Current.Adapter.Tree.binaryValue (List.ofFn fun i : Fin 10 =>
      Bool.xor (MdocAdvice.bits otp tree i) (MdocAdvice.bits masked tree i)) =
        (quotients tree).val := by
  dsimp only
  have heq : (fun i : Fin 10 => Bool.xor
      (MdocAdvice.bits ((AdapterBits.xorValue quotients).symm masked) tree i)
      (MdocAdvice.bits masked tree i)) = fun i : Fin 10 => (quotients tree).val.testBit i.val := by
    funext i
    rw [AdapterBits.xorValue_symm_bits]
    cases MdocAdvice.bits masked tree i <;> simp [MdocAdvice.bits]
  rw [heq]
  exact AdapterBits.binaryValue_word (quotients tree)

/-- A product check for the decoded quotient makes one tree's virtual leaves
multiply to one: the fixed fragment's check on that tree holds. -/
theorem product_check_leaves {B Source : Type} [Field B] [CharP B 2] (hd : 0 < d)
    (generator : Bˣ) (weights : Fin d → ZMod p) (target alpha : ZMod p)
    (sources : Fin d → Source) (pads : Fin q → Source) (masked : Fin q → Bool) (bits : Source → Bool)
    (hproduct : Current.Adapter.ProductCheck generator weights (bits ∘ sources) target alpha
      (Current.Adapter.Tree.binaryValue (List.ofFn fun i => Bool.xor (bits (pads i)) (masked i)))) :
    ∏ i, (Current.Adapter.Leaves.tree sources (fun j => generator^(alpha*weights j).val) pads
      (generator^(-(p : ℤ))) masked (generator^(alpha*target).val) i).value
        (Current.Adapter.Circuit.bitValue ∘ bits) = 1 :=
  (Current.Adapter.Leaves.tree_product_check hd generator weights target alpha sources pads masked bits).mpr
    hproduct

namespace Mdoc

/-- The committed bits read by the virtual leaves: the original 768 bits,
the canonical bits of the same recovered prime scalar, and the recovered
quotient pads. Public source maps place these values in the application. -/
def recoveredInputs (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P)
    (alpha : Alphas) (mu : P) (masked : MdocAdvice.Value) :
    Fin 1024 ⊕ (Fin 2 × Fin 10) → Bool :=
  Sum.elim (values sharedWeights shared eta mu) fun ⟨tree,i⟩ =>
    MdocAdvice.bits ((AdapterBits.xorValue (advice sharedWeights shared eta alpha mu)).symm masked) tree i

/-- On the recovered bits, every tree's virtual leaves multiply to one. -/
theorem recoveredInputs_satisfy {B : Type} [Field B] [CharP B 2] (generator : Bˣ)
    (sharedWeights : Fin 768 → P) (shared : Fin 768 → Bool) (eta : P) (alpha : Alphas)
    (mu : P) (masked : MdocAdvice.Value) (tree : Fin 2) :
    ∏ i, (Current.Adapter.Leaves.tree Sum.inl
      (fun j => generator^((alpha mu tree).val*weights sharedWeights eta j).val)
      (fun i => Sum.inr (tree,i)) (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ)))
      (MdocAdvice.bits masked tree) (generator^((alpha mu tree).val*mu).val) i).value
        (Current.Adapter.Circuit.bitValue ∘ recoveredInputs sharedWeights shared eta alpha mu masked) = 1 := by
  apply product_check_leaves (by decide)
  change Current.Adapter.ProductCheck generator (weights sharedWeights eta)
    (values sharedWeights shared eta mu) mu (alpha mu tree).val _
  dsimp only [recoveredInputs,advice,Sum.elim_inr]
  rw [recovered_advice]
  exact honest_product_check generator _ _ _ _ (by decide) (residual_zero _ _ _ _)

end Mdoc
end LfzkV2.Current.ZeroKnowledge.Frontend.Adapter
