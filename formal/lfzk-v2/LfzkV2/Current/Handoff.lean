import LfzkV2.Current.Adapter
import LfzkV2.Current.PrimeClaim

/-! The product-tree equations and the prime affine row authenticate the same
shared-input claim. The binary mask is reconstructed from its committed bits;
the prime mask is a separate recovered cell. Their equality is a conclusion
outside the rescaling event, not a premise. -/
namespace LfzkV2.Current.Handoff
open Finset SumcheckV2

variable {p shared maskBits : ℕ} [Fact p.Prime]

def binaryMask (mask : Fin maskBits → Bool) : ZMod p :=
  ∑ i, if mask i then (2 : ZMod p)^i.val else 0

def values (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool) :
    Fin (shared+maskBits) → Bool := Fin.addCases sharedValues mask

/-- The public adapter weights are eta times the shared-input weights,
followed by the ordinary binary expansion of the hiding scalar. -/
def weights (sharedWeights : Fin shared → ZMod p) (eta : ZMod p) :
    Fin (shared+maskBits) → ZMod p :=
  Fin.addCases (fun i => eta * sharedWeights i) (fun i => 2^i.val)

theorem residual_eq (sharedWeights : Fin shared → ZMod p) (eta mu : ZMod p)
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool) :
    Adapter.residual (weights sharedWeights eta) (values sharedValues mask) mu =
      eta * (∑ i, sharedWeights i * (if sharedValues i then 1 else 0)) +
        binaryMask mask - mu := by
  simp [Adapter.residual, weights, values, Fin.sum_univ_add, binaryMask,
    mul_ite, mul_sum]

def ConversionBad (sharedWeights : Fin shared → ZMod p) (eta mu : ZMod p)
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool) (M K : ℕ)
    (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p)) : Prop :=
  Adapter.residual (weights sharedWeights eta) (values sharedValues mask) mu ≠ 0 ∧
    ∀ j, Adapter.Bad (weights sharedWeights eta) (values sharedValues mask) mu M K (alpha j)

variable {Other G : Type} [Fintype Other] [CommGroup G]

/-- The only escapes in this handoff are the counted rescaling root and the
two-challenge conversion collision. Quotients may depend on both challenges;
the latter event includes every permitted pair of quotient values. -/
theorem product_handoff (generator : G) {M K : ℕ} (horder : orderOf generator = M)
    (claim : Prime.Claim (Fin shared) Other (ZMod p))
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool) (other : Other → ZMod p)
    (eta mu primeMask : ZMod p) (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p))
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (hproducts : ∀ j, Adapter.ProductCheck generator (weights claim.sharedWeights eta)
      (values sharedValues mask) mu (alpha j).val (quotient j))
    (hrow : (claim.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0) :
    (claim.residual (fun i => if sharedValues i then 1 else 0) other = 0 ∧
      binaryMask mask = primeMask) ∨
    Prime.RescalingBad (claim.residual (fun i => if sharedValues i then 1 else 0) other)
      (binaryMask mask - primeMask) eta ∨
    ConversionBad claim.sharedWeights eta mu sharedValues mask M K alpha := by
  by_cases hzero : Adapter.residual (weights claim.sharedWeights eta)
      (values sharedValues mask) mu = 0
  · have hopen : mu = eta * (∑ i, claim.sharedWeights i * (if sharedValues i then 1 else 0)) +
        binaryMask mask := by
      rw [residual_eq, sub_eq_zero] at hzero
      exact hzero.symm
    rcases claim.true_or_rescaling_bad (fun i => if sharedValues i then 1 else 0)
      other eta mu (binaryMask mask) primeMask hopen hrow with htrue | hbad
    · exact Or.inl htrue
    · exact Or.inr (Or.inl hbad)
  · refine Or.inr (Or.inr ⟨hzero,fun j => ?_⟩)
    exact ⟨quotient j, hquotient j,
      (Adapter.product_check_iff generator horder _ _ _ _ _).mp (hproducts j)⟩

/-- The unbatched mixed-storage handoff. The prime statement is the layer
rows followed by the native row; the layer rows are authenticated directly,
and the input equation only through rescaling and the conversion proof. No
row-combination challenge precedes eta. -/
theorem split_handoff (claim : Prime.Claim (Fin shared) Other (ZMod p)) (generator : G) {M K : ℕ}
    (horder : orderOf generator = M)
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool) (other : Other → ZMod p)
    (eta mu primeMask : ZMod p) (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p))
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (hproducts : ∀ j, Adapter.ProductCheck generator (weights claim.sharedWeights eta)
      (values sharedValues mask) mu (alpha j).val (quotient j))
    (hrows : RowsHold (claim.rows eta mu) (Sum.elim other (fun _ => primeMask))) :
    (RowsHold claim.layers other ∧
        claim.residual (fun i => if sharedValues i then 1 else 0) other = 0) ∨
      Prime.RescalingBad (claim.residual (fun i => if sharedValues i then 1 else 0) other)
        (binaryMask mask - primeMask) eta ∨
      ConversionBad claim.sharedWeights eta mu sharedValues mask M K alpha := by
  obtain ⟨hlayers,hrow⟩ := (claim.rows_hold_iff eta mu primeMask other).mp hrows
  rcases product_handoff generator horder claim sharedValues mask other eta mu primeMask
    alpha quotient hquotient hproducts hrow with htrue | hscale | hconversion
  · exact Or.inl ⟨hlayers,htrue.1⟩
  · exact Or.inr (Or.inl hscale)
  · exact Or.inr (Or.inr hconversion)
end LfzkV2.Current.Handoff
