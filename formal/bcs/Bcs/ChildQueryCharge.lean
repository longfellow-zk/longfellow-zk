import Bcs.PotentialOracle
import Bcs.FirstPairCombined

/-! One fresh child answer, even when the parent is queried later. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- An indexed child-query event costs one local answer budget per queried
child point.  The event may depend on all other oracle answers, including its
parent's answer; only the child answer must remain fresh. -/
theorem tree_child_indexed_weight_ratio_le
    {Q C Out I : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype I] {N : ℕ}
    (tree : Tree Q C Out N)
    (child : I → Q) (hchild : Function.Injective child)
    (weight : I → (Q → C) → C → ℚ)
    (hoff : ∀ i H H', AgreeOff (child i) H H' →
      ∀ c, weight i H c = weight i H' c)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hlocal : ∀ i H, ∑ c : C, weight i H c ≤ beta) :
    (∑ H : Q → C, ∑ i : I,
      if child i ∈ queried tree H then
        weight i H (H (child i)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N : ℚ) * beta / Fintype.card C := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  let W (i : I) (H : Q → C) (c : C) : ℚ :=
    if child i ∈ queried tree H then weight i H c else 0
  have hWoff (i : I) (H H' : Q → C)
      (h : AgreeOff (child i) H H') (c : C) :
      W i H c = W i H' c := by
    have hmem := mem_queried_iff tree (child i) h
    by_cases hi : child i ∈ queried tree H
    · have hi' := hmem.mp hi
      simp [W, hi, hi', hoff i H H' h c]
    · have hi' := mt hmem.mpr hi
      simp [W, hi, hi']
  have hcoord (i : I) :
      (∑ H : Q → C, W i H (H (child i))) * q =
        ∑ H : Q → C, ∑ c : C, W i H c :=
    sum_coord_mul_rat (child i) (W i) (hWoff i)
  have hcount (H : Q → C) :
      ((univ.filter fun i : I => child i ∈ queried tree H).card : ℚ) ≤ N := by
    let s := (univ : Finset I).filter
      (fun i => child i ∈ queried tree H)
    have hinj : (s.image child).card = s.card :=
      Finset.card_image_of_injOn
        (fun i _ j _ hij => hchild hij)
    have hsub : s.image child ⊆ (queried tree H).toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
      subst x
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2
    have hc : s.card ≤ N := by
      calc
        _ = (s.image child).card := hinj.symm
        _ ≤ (queried tree H).toFinset.card := Finset.card_le_card hsub
        _ ≤ N := (List.toFinset_card_le _).trans (queried_length_le tree H)
    exact_mod_cast hc
  have hsum :
      q * (∑ H : Q → C, ∑ i : I, W i H (H (child i))) ≤
      (N : ℚ) * beta * q ^ Fintype.card Q := by
    calc
      _ = (∑ i : I, ∑ H : Q → C, W i H (H (child i))) * q := by
        rw [Finset.sum_comm]
        ring
      _ = ∑ i : I, (∑ H : Q → C, W i H (H (child i))) * q := by
        rw [Finset.sum_mul]
      _ = ∑ i : I, ∑ H : Q → C, ∑ c : C, W i H c := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcoord i
      _ = ∑ H : Q → C, ∑ i : I, ∑ c : C, W i H c :=
        Finset.sum_comm
      _ ≤ ∑ H : Q → C, (N : ℚ) * beta := by
        apply Finset.sum_le_sum
        intro H _
        calc
          (∑ i : I, ∑ c : C, W i H c) ≤
              ∑ i : I, if child i ∈ queried tree H then beta else 0 := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi : child i ∈ queried tree H
            · simpa only [W, hi, ↓reduceIte] using hlocal i H
            · simp [W, hi]
          _ = ((univ.filter fun i : I =>
              child i ∈ queried tree H).card : ℚ) * beta := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, mul_comm]
          _ ≤ N * beta :=
            mul_le_mul_of_nonneg_right (hcount H) hbeta
      _ = (N : ℚ) * beta * q ^ Fintype.card Q := by
        simp [q, mul_comm]
  have hden : 0 < q ^ Fintype.card Q := pow_pos hq _
  change (∑ H : Q → C, ∑ i : I,
      if child i ∈ queried tree H then
        weight i H (H (child i)) else 0) /
      q ^ Fintype.card Q ≤ (N : ℚ) * beta / q
  rw [div_le_div_iff₀ hden hq]
  simpa only [W, mul_comm] using hsum

end Bcs.TotalOracle
