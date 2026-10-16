import Bcs.TotalOracle

/-!
# Which of two oracle inputs an adaptive search sees first

The identity of the first queried point among `x` and `y` is determined
before either answer is read.  This is the freshness fact needed to split
the terminal parent/child analysis by query order when the child input
contains the response message but not the raw parent challenge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Merkle.RandomOracle

inductive FirstOfTwo where
  | neither
  | left
  | right
  deriving DecidableEq

/-- First queried point among `x` and `y`, ignoring any later queries. -/
def firstOfTwo {Q C Out : Type} {fuel : ℕ}
    [DecidableEq Q] (tree : Tree Q C Out fuel) (H : Q → C) (x y : Q) : FirstOfTwo :=
  match tree with
  | .done _ => .neither
  | .query q next =>
      if q = x then .left
      else if q = y then .right
      else firstOfTwo (next (H q)) H x y

/-- Reprogramming either answer leaves the identity of the first query of
the pair unchanged.  The prover may query other inputs adaptively. -/
theorem firstOfTwo_congr_off {Q C Out : Type} {fuel : ℕ}
    [DecidableEq Q]
    (tree : Tree Q C Out fuel) (H H' : Q → C) (x y : Q)
    (hagrees : ∀ q, q ≠ x → q ≠ y → H q = H' q) :
    firstOfTwo tree H x y = firstOfTwo tree H' x y := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
      by_cases hx : q = x
      · simp only [firstOfTwo, if_pos hx]
      · by_cases hy : q = y
        · simp only [firstOfTwo, if_neg hx, if_pos hy]
        · have hq : H q = H' q := hagrees q hx hy
          simp only [firstOfTwo, if_neg hx, if_neg hy, hq]
          exact ih (H' q)

/-- A left first hit really is an adversarial query of `x`. -/
theorem firstOfTwo_left_mem {Q C Out : Type} {fuel : ℕ}
    [DecidableEq Q]
    (tree : Tree Q C Out fuel) (H : Q → C) (x y : Q)
    (h : firstOfTwo tree H x y = .left) :
    x ∈ queried tree H := by
  induction tree with
  | done _ => simp [firstOfTwo] at h
  | query q next ih =>
      by_cases hx : q = x
      · simp [queried_query, hx]
      · by_cases hy : q = y
        · simp only [firstOfTwo, if_neg hx, if_pos hy] at h
          cases h
        · simp only [firstOfTwo, if_neg hx, if_neg hy] at h
          simp only [queried_query, List.mem_cons]
          exact Or.inr (ih (H q) h)

/-- A right first hit really is an adversarial query of `y`. -/
theorem firstOfTwo_right_mem {Q C Out : Type} {fuel : ℕ}
    [DecidableEq Q]
    (tree : Tree Q C Out fuel) (H : Q → C) (x y : Q)
    (h : firstOfTwo tree H x y = .right) :
    y ∈ queried tree H := by
  induction tree with
  | done _ => simp [firstOfTwo] at h
  | query q next ih =>
      by_cases hx : q = x
      · simp only [firstOfTwo, if_pos hx] at h
        cases h
      · by_cases hy : q = y
        · simp [queried_query, hy]
        · simp only [firstOfTwo, if_neg hx, if_neg hy] at h
          simp only [queried_query, List.mem_cons]
          exact Or.inr (ih (H q) h)

/-- If the right point is queried, the first hit of the pair exists. -/
theorem firstOfTwo_ne_neither_of_right_mem {Q C Out : Type} {fuel : ℕ}
    [DecidableEq Q]
    (tree : Tree Q C Out fuel) (H : Q → C) (x y : Q)
    (hy : y ∈ queried tree H) : firstOfTwo tree H x y ≠ .neither := by
  induction tree with
  | done _ => simp at hy
  | query q next ih =>
      rw [queried_query] at hy
      by_cases hx : q = x
      · simp [firstOfTwo, hx]
      · by_cases hqy : q = y
        · simp only [firstOfTwo]
          split_ifs; decide
        · simp only [List.mem_cons] at hy
          rcases hy with hy | hy
          · exact False.elim (hqy hy.symm)
          · simpa [firstOfTwo, hx, hqy] using ih (H q) hy

end Bcs.TotalOracle
