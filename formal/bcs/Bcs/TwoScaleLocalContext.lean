import Bcs.FirstPairLocalContext
import Bcs.ChildQueryCharge

/-! Low and high terminal charges with a parent-indexed off-pair context. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- A field-dependent low one-answer budget and grouped high two-answer
budget share one adaptive query count.  The parent-indexed context is unchanged when
either terminal answer is resampled. -/
theorem tree_two_scale_local_context_ratio_le
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
    (low high : State → Parent → Response → C → C → Prop)
    (betaLow betaHigh : ℚ)
    (hbetaLow : 0 ≤ betaLow) (hbetaHigh : 0 ≤ betaHigh)
    (hlow : ∀ s p r a,
      ∑ b : C, (if low s p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C * betaLow)
    (hhigh : ∀ s p,
      ∑ r : Response, ∑ a : C, ∑ b : C,
        (if high s p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * betaHigh) :
    (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
      ((if child p r ∈ queried tree H ∧
          low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
          high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0))) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * (betaLow + betaHigh) := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  let lowWeight (i : Parent × Response) (H : Q → C) (b : C) : ℚ :=
    if low (state i.1 H) i.1 i.2 (H (parent i.1)) b then 1 else 0
  have hlowOff (i : Parent × Response) (H H' : Q → C)
      (h : AgreeOff (child i.1 i.2) H H') (b : C) :
      lowWeight i H b = lowWeight i H' b := by
    have hs : state i.1 H = state i.1 H' :=
      hstateOff i.1 i.2 H H' (fun z _ hz => h z hz)
    have hp : H (parent i.1) = H' (parent i.1) :=
      h (parent i.1) (hdisjoint i.1 i.1 i.2)
    simp [lowWeight, hs, hp]
  have hlowLocal (i : Parent × Response) (H : Q → C) :
      ∑ b : C, lowWeight i H b ≤ q * betaLow :=
    hlow (state i.1 H) i.1 i.2 (H (parent i.1))
  have hlowBound := tree_child_indexed_weight_ratio_le tree
    (fun i : Parent × Response => child i.1 i.2)
    hchild lowWeight hlowOff (q * betaLow)
    (mul_nonneg hq.le hbetaLow) hlowLocal
  let highWeight (s : State) (p : Parent) (r : Response)
      (a b : C) : ℚ := if high s p r a b then 1 else 0
  let highBudget (s : State) (p : Parent) (r : Response) : ℚ :=
    ∑ a : C, ∑ b : C, highWeight s p r a b
  have hhighNonneg (s : State) (p : Parent) (r : Response) :
      0 ≤ highBudget s p r := by
    dsimp [highBudget, highWeight]
    apply Finset.sum_nonneg
    intro a _
    exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
  have hhighLocal (s : State) (p : Parent) (r : Response) :
      ∑ a : C, ∑ b : C, highWeight s p r a b ≤ highBudget s p r := le_refl _
  have hhighBudget (s : State) (p : Parent) :
      ∑ r : Response, highBudget s p r ≤ q ^ 2 * betaHigh := by
    simpa only [highBudget, highWeight, q] using hhigh s p
  have hhighBound := tree_both_orders_local_context_ratio_le tree
    parent child hparent hchild hdisjoint state hstateOff
    highWeight highBudget hhighNonneg (q ^ 2 * betaHigh)
    (mul_nonneg (sq_nonneg q) hbetaHigh)
    hhighLocal hhighBudget
  have hlowBound' :
      (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
        if child p r ∈ queried tree H ∧
            low (state p H) p r (H (parent p)) (H (child p r)) then
          (1 : ℚ) else 0) / q ^ Fintype.card Q ≤ N * betaLow := by
    have h :
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if child p r ∈ queried tree H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q ≤
          N * (q * betaLow) / q := by
      simpa only [ite_and, Fintype.sum_prod_type, lowWeight, q]
        using hlowBound
    calc
      _ ≤ N * (q * betaLow) / q := h
      _ = N * betaLow := by field_simp [hq.ne']
  have hhighBound' :
      (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
        if firstOfTwoOffResult tree (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high (state p H) p r (H (parent p)) (H (child p r)) then
          (1 : ℚ) else 0) / q ^ Fintype.card Q ≤ N * betaHigh := by
    have h :
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if firstOfTwoOffResult tree (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q ≤
          N * (q ^ 2 * betaHigh) / q ^ 2 := by
      simpa only [ite_and, highWeight, q] using hhighBound
    calc
      _ ≤ N * (q ^ 2 * betaHigh) / q ^ 2 := h
      _ = N * betaHigh := by field_simp [hq.ne']
  calc
    _ = (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if child p r ∈ queried tree H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q +
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if firstOfTwoOffResult tree (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q := by
          simp only [Finset.sum_add_distrib, add_div, q]
    _ ≤ N * betaLow + N * betaHigh :=
      add_le_add hlowBound' hhighBound'
    _ = N * (betaLow + betaHigh) := by ring

end Bcs.TotalOracle
