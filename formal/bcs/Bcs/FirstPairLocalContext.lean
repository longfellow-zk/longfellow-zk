import Bcs.FirstPairPath
import Bcs.TwoCoordinatePotential

/-! Pair-indexed off-answer context for grouped first-pair charging. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- The context may vary with the selected parent.  For each parent it is
fixed when that parent's answer and any one of its child answers are
resampled.  Other query-role answers remain available to the context. -/
theorem tree_both_orders_local_context_ratio_le
    {Q C Out Parent Response State : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r (H H' : Q → C),
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (weight : State → Parent → Response → C → C → ℚ)
    (budget : State → Parent → Response → ℚ)
    (hnonneg : ∀ s p r, 0 ≤ budget s p r)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hlocal : ∀ s p r,
      ∑ a : C, ∑ b : C, weight s p r a b ≤ budget s p r)
    (hsumBudget : ∀ s p, ∑ r : Response, budget s p r ≤ beta) :
    (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
      if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
        weight (state p H) p r (H (parent p)) (H (child p r)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * beta / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let stateOff (p : Parent) (r : Response)
      (off : AwayFromTwo (parent p) (child p r) → C) : State :=
    state p ((splitTwo (C := C) (parent p) (child p r)
      (hdisjoint p p r)).symm
      (off, (Classical.choice inferInstance, Classical.choice inferInstance)))
  have hstateEq (p : Parent) (r : Response) (H : Q → C) :
      stateOff p r (fun z => H z.1) = state p H := by
    apply hstateOff p r
    intro z hx hy
    simp [splitTwo, hx, hy]
  have hpath (H : Q → C) :
      (∑ p : Parent, ∑ r : Response,
        if firstOfTwoOffResult tree (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
          budget (state p H) p r else 0) ≤ (N : ℚ) * beta :=
    tree_first_pair_grouped_path_le tree parent child hparent hchild
      hdisjoint (fun p r => budget (state p H) p r)
      (fun p r => hnonneg (state p H) p r) beta hbeta
      (fun p => hsumBudget (state p H) p) H
  have h := charged_two_fresh_weight_ratio_le_dynamic
    (I := Parent × Response)
    (fun i => parent i.1) (fun i => child i.1 i.2)
    (fun i => hdisjoint i.1 i.1 i.2)
    (fun i off => firstOfTwoOffResult tree (parent i.1) (child i.1 i.2)
      (hdisjoint i.1 i.1 i.2) off ≠ .neither)
    (fun i off a b => weight (stateOff i.1 i.2 off) i.1 i.2 a b)
    (fun i off => budget (stateOff i.1 i.2 off) i.1 i.2)
    (N * beta)
    (fun i off => hlocal (stateOff i.1 i.2 off) i.1 i.2)
    (fun H => by
      simp only [Fintype.sum_prod_type]
      simp_rw [hstateEq]
      exact hpath H)
  simpa only [Fintype.sum_prod_type, hstateEq] using h

end Bcs.TotalOracle
