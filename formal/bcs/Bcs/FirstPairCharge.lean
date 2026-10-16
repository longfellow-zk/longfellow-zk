import Bcs.FirstPairQuery
import Bcs.TwoCoordinatePotential

/-!
# Adaptive child-before-parent pair charging

A child input determines its parent input from its message prefix.  If the
prover queries the child before the parent, the first-query decision reads
neither of their answers.  Thus a two-fresh-coordinate pair bound may be
charged once for that child query.  There are at most `N` such queried child
inputs in an `N`-query adversary tree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

variable {Q C Out : Type} [Fintype Q] [DecidableEq Q]
  [Fintype C] [Nonempty C]
variable {N : ℕ}

/-- Evaluate the first-hit decision using a canonical representative of a
fixed off-pair oracle.  The result is independent of the representative's
two answers by `firstOfTwo_congr_off`. -/
noncomputable def firstOfTwoOff (tree : Tree Q C Out N)
    (x y : Q) (hxy : x ≠ y) (off : AwayFromTwo x y → C) : Prop :=
  let e := splitTwo (C := C) x y hxy
  firstOfTwo tree (e.symm (off, (Classical.choice inferInstance,
    Classical.choice inferInstance))) x y = .left

omit [Fintype Q] [Fintype C] in
/-- The canonical off-pair decision agrees with the actual adaptive run. -/
theorem firstOfTwoOff_iff (tree : Tree Q C Out N)
    (x y : Q) (hxy : x ≠ y) (H : Q → C) :
    firstOfTwoOff tree x y hxy (fun z => H z.1) ↔
      firstOfTwo tree H x y = .left := by
  let e := splitTwo (C := C) x y hxy
  let H' := e.symm ((fun z : AwayFromTwo x y => H z.1),
    (Classical.choice inferInstance, Classical.choice inferInstance))
  have hoff : ∀ q, q ≠ x → q ≠ y → H' q = H q := by
    intro q hx hy
    have hproj := congrArg Prod.fst (e.right_inv
      ((fun z : AwayFromTwo x y => H z.1),
        (Classical.choice inferInstance, Classical.choice inferInstance)))
    have hq := congrFun hproj ⟨q, hx, hy⟩
    exact hq
  have hfirst := firstOfTwo_congr_off tree H' H x y hoff
  change firstOfTwo tree H' x y = .left ↔
    firstOfTwo tree H x y = .left
  rw [hfirst]

/-- Specialize the first-hit decision to a child and its fixed parent. -/
noncomputable def childFirstOff (tree : Tree Q C Out N)
    (mate : Q → Q) (hneq : ∀ x, x ≠ mate x)
    (x : Q) (off : AwayFromTwo x (mate x) → C) : Prop :=
  firstOfTwoOff tree x (mate x) (hneq x) off

omit [Fintype Q] [Fintype C] in
theorem childFirstOff_iff (tree : Tree Q C Out N)
    (mate : Q → Q) (hneq : ∀ x, x ≠ mate x)
    (x : Q) (H : Q → C) :
    childFirstOff tree mate hneq x (fun z => H z.1) ↔
      firstOfTwo tree H x (mate x) = .left :=
  firstOfTwoOff_iff tree x (mate x) (hneq x) H

omit [Fintype C] in
/-- At most `N` points can be selected as the first queried member of their
own child/parent pair, regardless of the adaptive query order. -/
theorem childFirstOff_card_le (tree : Tree Q C Out N)
    (mate : Q → Q) (hneq : ∀ x, x ≠ mate x)
    (H : Q → C) :
    (univ.filter fun x : Q =>
      childFirstOff tree mate hneq x (fun z => H z.1)).card ≤ N := by
  have hsub : (univ.filter fun x : Q =>
      childFirstOff tree mate hneq x (fun z => H z.1)) ⊆
      (queried tree H).toFinset := by
    intro x hx
    have hfirst : firstOfTwo tree H x (mate x) = .left :=
      (childFirstOff_iff tree mate hneq x H).mp (Finset.mem_filter.mp hx).2
    exact List.mem_toFinset.mpr (firstOfTwo_left_mem tree H x (mate x) hfirst)
  exact (Finset.card_le_card hsub).trans
    ((List.toFinset_card_le _).trans (queried_length_le tree H))

/-- The complete `N`-query bound for an early child whose fixed parent is
`mate x`.  The pathwise acceptance-to-charge implication is supplied by the
protocol instance; this theorem supplies its adaptive probability cost. -/
theorem tree_child_first_weight_ratio_le (tree : Tree Q C Out N)
    (mate : Q → Q) (hneq : ∀ x, x ≠ mate x)
    (weight : ∀ x, (AwayFromTwo x (mate x) → C) → C → C → ℚ)
    (budget : ℚ) (hbudget : 0 ≤ budget)
    (hlocal : ∀ x off,
      ∑ a : C, ∑ b : C, weight x off a b ≤ budget) :
    (∑ H : Q → C, ∑ x : Q,
      if childFirstOff tree mate hneq x (fun z => H z.1) then
        weight x (fun z => H z.1) (H x) (H (mate x)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * budget / (Fintype.card C : ℚ) ^ 2 := by
  apply charged_two_fresh_weight_ratio_le (fun x => x) mate hneq
    (childFirstOff tree mate hneq) weight (fun _ => budget)
    (N * budget)
  · exact hlocal
  · intro H
    have hcard := childFirstOff_card_le tree mate hneq H
    calc
      (∑ x : Q,
        if childFirstOff tree mate hneq x (fun z => H z.1) then budget else 0) =
        ((univ.filter fun x : Q =>
          childFirstOff tree mate hneq x (fun z => H z.1)).card : ℚ) * budget := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, mul_comm]
      _ ≤ N * budget :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbudget

/-- A parent queried before a possible child is charged once per parent,
even when many complete response messages yield different child inputs.
The per-response pair budgets are summed *before* charging the at-most-`N`
parent queries.  This is the high-agreement half of the grouped-response
compiler; the child point for a fixed response is independent of the raw
parent answer. -/
theorem tree_parent_first_grouped_weight_ratio_le
    {Response : Type} [Fintype Response]
    (tree : Tree Q C Out N)
    (child : Q → Response → Q)
    (hneq : ∀ x response, x ≠ child x response)
    (weight : ∀ x response,
      (AwayFromTwo x (child x response) → C) → C → C → ℚ)
    (budget : Q → Response → ℚ)
    (hbudget : ∀ x response, 0 ≤ budget x response)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hlocal : ∀ x response off,
      ∑ a : C, ∑ b : C, weight x response off a b ≤ budget x response)
    (hsumBudget : ∀ x, ∑ response : Response, budget x response ≤ beta) :
    (∑ H : Q → C, ∑ x : Q, ∑ response : Response,
      if firstOfTwoOff tree x (child x response) (hneq x response)
          (fun z => H z.1) then
        weight x response (fun z => H z.1)
          (H x) (H (child x response)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * beta / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let charged (i : Q × Response)
      (off : AwayFromTwo i.1 (child i.1 i.2) → C) : Prop :=
    firstOfTwoOff tree i.1 (child i.1 i.2) (hneq i.1 i.2) off
  have htotal (H : Q → C) :
      (∑ i : Q × Response,
        if charged i (fun z => H z.1) then budget i.1 i.2 else 0) ≤
      N * beta := by
    rw [Fintype.sum_prod_type]
    have hpoint (x : Q) :
        (∑ response : Response,
          if charged (x, response) (fun z => H z.1) then
            budget x response else 0) ≤
          if x ∈ queried tree H then beta else 0 := by
      by_cases hx : x ∈ queried tree H
      · simp only [hx, ↓reduceIte]
        calc
          _ ≤ ∑ response : Response, budget x response := by
            apply Finset.sum_le_sum
            intro response _
            by_cases hc : charged (x, response) (fun z => H z.1)
            · simp [hc]
            · simpa [hc] using hbudget x response
          _ ≤ beta := hsumBudget x
      · have hfalse (response : Response) :
            ¬ charged (x, response) (fun z => H z.1) := by
          intro hc
          have hf : firstOfTwo tree H x (child x response) = .left :=
            (firstOfTwoOff_iff tree x (child x response)
              (hneq x response) H).mp hc
          exact hx (firstOfTwo_left_mem tree H x (child x response) hf)
        simp [hx, hfalse]
    calc
      (∑ x : Q, ∑ response : Response,
          if charged (x, response) (fun z => H z.1) then
            budget x response else 0) ≤
        ∑ x : Q, if x ∈ queried tree H then beta else 0 :=
          Finset.sum_le_sum fun x _ => hpoint x
      _ = ((queried tree H).toFinset.card : ℚ) * beta := by
        rw [← Finset.sum_filter]
        have hset : (univ.filter fun x : Q => x ∈ queried tree H) =
            (queried tree H).toFinset := by
          ext x
          simp
        rw [hset]
        simp [Finset.sum_const, mul_comm]
      _ ≤ N * beta := by
        have hcard : (queried tree H).toFinset.card ≤ N :=
          (List.toFinset_card_le _).trans (queried_length_le tree H)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbeta
  have h := charged_two_fresh_weight_ratio_le
    (I := Q × Response) (fun i => i.1) (fun i => child i.1 i.2)
    (fun i => hneq i.1 i.2) charged
    (fun i off a b => weight i.1 i.2 off a b)
    (fun i => budget i.1 i.2) (N * beta)
    (fun i off => hlocal i.1 i.2 off) htotal
  simpa only [Fintype.sum_prod_type, charged] using h

end Bcs.TotalOracle
