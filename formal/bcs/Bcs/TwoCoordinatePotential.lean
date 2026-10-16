import Bcs.TwoFreshCoordinates

/-!
# Charging a bounded set of pairs of fresh oracle coordinates

This is the two-coordinate analogue of `PotentialOracle.charged_rational_sum_le`.
For each charged point `x`, its paired point `mate x` is fixed by `x`, and
whether `x` is charged reads neither answer.  A pair-count budget is charged
only for the points selected on the actual oracle.  In a transcript proof,
this handles a child query made before its parent challenge: the child input
already determines its parent prefix input.  The proof that the first-query
selection has the required freshness is an adversary-tree obligation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

theorem charged_two_fresh_weight_ratio_le
    {Q C I : Type} [Fintype Q] [DecidableEq Q] [Fintype I]
    [Fintype C] [Nonempty C]
    (first second : I → Q) (hneq : ∀ i, first i ≠ second i)
    (charged : ∀ i, (AwayFromTwo (first i) (second i) → C) → Prop)
    (weight : ∀ i, (AwayFromTwo (first i) (second i) → C) → C → C → ℚ)
    (budget : I → ℚ) (total : ℚ)
    (hlocal : ∀ i off,
      ∑ a : C, ∑ b : C, weight i off a b ≤ budget i)
    (htotal : ∀ H : Q → C,
      (∑ i : I, if charged i (fun z => H z.1) then budget i else 0) ≤ total) :
    (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      total / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  have hden : 0 < q ^ Fintype.card Q := pow_pos hq _
  have hpair (i : I) :
      q ^ 2 * (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      ∑ H : Q → C,
        if charged i (fun z => H z.1) then budget i else 0 := by
    let Off := AwayFromTwo (first i) (second i) → C
    have hw := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off a b => if charged i off then weight i off a b else 0)
    have hb := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off _ _ => if charged i off then budget i else 0)
    have hle :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then weight i off a b else 0) ≤
        ∑ off : Off,
          if charged i off then budget i else 0 := by
      apply Finset.sum_le_sum
      intro off _
      by_cases hc : charged i off
      · simpa only [hc, ↓reduceIte] using hlocal i off
      · simp [hc]
    have hconst :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then budget i else 0) =
        q ^ 2 * ∑ off : Off,
          if charged i off then budget i else 0 := by
      simp [q, pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
    change q ^ 2 *
      (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤ _
    rw [hw, hb, hconst]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt (pow_pos hq 2))
  have hsum :
      q ^ 2 * (∑ H : Q → C, ∑ i : I,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      total * q ^ Fintype.card Q := by
    calc
      _ = ∑ i : I, q ^ 2 * (∑ H : Q → C,
          if charged i (fun z => H z.1) then
            weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) := by
              rw [Finset.sum_comm]
              simp only [Finset.mul_sum]
      _ ≤ ∑ i : I, ∑ H : Q → C,
          if charged i (fun z => H z.1) then budget i else 0 :=
            Finset.sum_le_sum fun i _ => hpair i
      _ = ∑ H : Q → C, ∑ i : I,
          if charged i (fun z => H z.1) then budget i else 0 := Finset.sum_comm
      _ ≤ ∑ _H : Q → C, total :=
        Finset.sum_le_sum fun H _ => htotal H
      _ = total * q ^ Fintype.card Q := by
        simp [q, mul_comm]
  change (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
      q ^ Fintype.card Q ≤ total / q ^ 2
  rw [div_le_div_iff₀ hden (pow_pos hq 2)]
  simpa only [mul_comm] using hsum

end Bcs.TotalOracle

namespace Bcs.TotalOracle

open Finset
open scoped Classical

/-- Two-coordinate charging with a budget that may depend on all oracle
answers outside the charged pair.  This is needed when the verifier's later
statement depends on earlier field challenges that were not re-absorbed into
the message prefix. -/
theorem charged_two_fresh_weight_ratio_le_dynamic
    {Q C I : Type} [Fintype Q] [DecidableEq Q] [Fintype I]
    [Fintype C] [Nonempty C]
    (first second : I → Q) (hneq : ∀ i, first i ≠ second i)
    (charged : ∀ i, (AwayFromTwo (first i) (second i) → C) → Prop)
    (weight : ∀ i, (AwayFromTwo (first i) (second i) → C) → C → C → ℚ)
    (budget : ∀ i, (AwayFromTwo (first i) (second i) → C) → ℚ)
    (total : ℚ)
    (hlocal : ∀ i off,
      ∑ a : C, ∑ b : C, weight i off a b ≤ budget i off)
    (htotal : ∀ H : Q → C,
      (∑ i : I, if charged i (fun z => H z.1) then
        budget i (fun z => H z.1) else 0) ≤ total) :
    (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      total / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  have hden : 0 < q ^ Fintype.card Q := pow_pos hq _
  have hpair (i : I) :
      q ^ 2 * (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      ∑ H : Q → C,
        if charged i (fun z => H z.1) then
          budget i (fun z => H z.1) else 0 := by
    let Off := AwayFromTwo (first i) (second i) → C
    have hw := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off a b => if charged i off then weight i off a b else 0)
    have hb := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off _ _ => if charged i off then budget i off else 0)
    have hle :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then weight i off a b else 0) ≤
        ∑ off : Off,
          if charged i off then budget i off else 0 := by
      apply Finset.sum_le_sum
      intro off _
      by_cases hc : charged i off
      · simpa only [hc, ↓reduceIte] using hlocal i off
      · simp [hc]
    have hconst :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then budget i off else 0) =
        q ^ 2 * ∑ off : Off,
          if charged i off then budget i off else 0 := by
      simp [q, pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
    change q ^ 2 *
      (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤ _
    rw [hw, hb, hconst]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt (pow_pos hq 2))
  have hsum :
      q ^ 2 * (∑ H : Q → C, ∑ i : I,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      total * q ^ Fintype.card Q := by
    calc
      _ = ∑ i : I, q ^ 2 * (∑ H : Q → C,
          if charged i (fun z => H z.1) then
            weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) := by
              rw [Finset.sum_comm]
              simp only [Finset.mul_sum]
      _ ≤ ∑ i : I, ∑ H : Q → C,
          if charged i (fun z => H z.1) then
            budget i (fun z => H z.1) else 0 :=
            Finset.sum_le_sum fun i _ => hpair i
      _ = ∑ H : Q → C, ∑ i : I,
          if charged i (fun z => H z.1) then
            budget i (fun z => H z.1) else 0 := Finset.sum_comm
      _ ≤ ∑ _H : Q → C, total :=
        Finset.sum_le_sum fun H _ => htotal H
      _ = total * q ^ Fintype.card Q := by
        simp [q, mul_comm]
  change (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
      q ^ Fintype.card Q ≤ total / q ^ 2
  rw [div_le_div_iff₀ hden (pow_pos hq 2)]
  simpa only [mul_comm] using hsum

end Bcs.TotalOracle
