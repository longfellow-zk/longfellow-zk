import Bcs.TwoFreshCoordinates

/-!
# A fixed parent and many dependent terminal response inputs

For a fixed parent hash input, its answer determines one final hash input per
complete response. The union over responses costs the *sum* of their
accepting-answer counts, not the maximum count times a worst-case list size.
This is the two-coordinate counting kernel for response-mass certificates.
An adaptive parent-selection theorem is separate: this result does not
charge a prover that first searches for a favorable parent input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

theorem fixed_parent_grouped_ratio_le
    {Q C Response : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Response]
    (parent : Q) (child : C → Response → Q)
    (hchild : ∀ c response, parent ≠ child c response)
    (bad : ∀ c response,
      (AwayFromTwo parent (child c response) → C) → C → C → Prop)
    (count : C → Response → ℕ)
    (hpair : ∀ c response (off : AwayFromTwo parent (child c response) → C),
      (univ.filter fun p : C × C =>
        p.1 = c ∧ bad c response off p.1 p.2).card ≤ count c response) :
    ((univ.filter fun H : Q → C =>
      ∃ response : Response,
        bad (H parent) response (fun z => H z.1)
          (H parent) (H (child (H parent) response))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      ((∑ c : C, ∑ response : Response, count c response : ℕ) : ℚ) /
        (Fintype.card C : ℚ) ^ 2 := by
  classical
  let A (response : Response) : Finset (Q → C) :=
    univ.filter fun H =>
      bad (H parent) response (fun z => H z.1)
        (H parent) (H (child (H parent) response))
  have hsub : (univ.filter fun H : Q → C =>
      ∃ response : Response,
        bad (H parent) response (fun z => H z.1)
          (H parent) (H (child (H parent) response))) ⊆
      univ.biUnion A := by
    intro H hH
    obtain ⟨response, hresponse⟩ := (Finset.mem_filter.mp hH).2
    exact Finset.mem_biUnion.mpr
      ⟨response, Finset.mem_univ _, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hresponse⟩⟩
  have hnum :
      (univ.filter fun H : Q → C =>
        ∃ response : Response,
          bad (H parent) response (fun z => H z.1)
            (H parent) (H (child (H parent) response))).card ≤
        ∑ response : Response, (A response).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hden : 0 ≤ (Fintype.card C : ℚ) ^ Fintype.card Q :=
    pow_nonneg (Nat.cast_nonneg _) _
  calc
    ((univ.filter fun H : Q → C =>
      ∃ response : Response,
        bad (H parent) response (fun z => H z.1)
          (H parent) (H (child (H parent) response))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      ((∑ response : Response, (A response).card : ℕ) : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q :=
          div_le_div_of_nonneg_right (by exact_mod_cast hnum) hden
    _ = ∑ response : Response,
          ((A response).card : ℚ) /
            (Fintype.card C : ℚ) ^ Fintype.card Q := by
              push_cast
              simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ response : Response,
          ((∑ c : C, count c response : ℕ) : ℚ) /
            (Fintype.card C : ℚ) ^ 2 := by
              apply Finset.sum_le_sum
              intro response _
              exact dependent_second_ratio_le parent
                (fun c => child c response)
                (fun c => hchild c response)
                (fun c off a d => bad c response off a d)
                (fun c => count c response)
                (fun c off => hpair c response off)
    _ = ((∑ c : C, ∑ response : Response,
          count c response : ℕ) : ℚ) /
            (Fintype.card C : ℚ) ^ 2 := by
              push_cast
              simp only [div_eq_mul_inv, Finset.sum_mul]
              rw [Finset.sum_comm]

/-- Rational version of the grouped parent/response count.  Its local
premise may use a fractional query-cover weight, so the analysis does not
round every radius to an integer accepting-answer count.  The parent input
is fixed; an adaptive search for that input still needs a tree compiler. -/
theorem fixed_parent_grouped_weight_ratio_le
    {Q C Response : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Response]
    (parent : Q) (child : C → Response → Q)
    (hchild : ∀ c response, parent ≠ child c response)
    (weight : ∀ c response,
      (AwayFromTwo parent (child c response) → C) → C → C → ℚ)
    (budget : C → Response → ℚ)
    (hlocal : ∀ c response
      (off : AwayFromTwo parent (child c response) → C),
      ∑ d : C, weight c response off c d ≤ budget c response) :
    (∑ H : Q → C, ∑ response : Response,
        weight (H parent) response (fun z => H z.1)
          (H parent) (H (child (H parent) response))) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (∑ c : C, ∑ response : Response, budget c response) /
        (Fintype.card C : ℚ) ^ 2 := by
  classical
  have hden : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) _
  calc
    (∑ H : Q → C, ∑ response : Response,
        weight (H parent) response (fun z => H z.1)
          (H parent) (H (child (H parent) response))) /
        (Fintype.card C : ℚ) ^ Fintype.card Q =
      ∑ response : Response,
        (∑ H : Q → C,
          weight (H parent) response (fun z => H z.1)
            (H parent) (H (child (H parent) response))) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            rw [Finset.sum_comm]
            simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ response : Response,
        (∑ c : C, budget c response) /
          (Fintype.card C : ℚ) ^ 2 := by
      apply Finset.sum_le_sum
      intro response _
      exact dependent_second_weight_ratio_le parent
        (fun c => child c response)
        (fun c => hchild c response)
        (fun c off a d => weight c response off a d)
        (fun c => budget c response)
        (fun c off => hlocal c response off)
    _ = (∑ c : C, ∑ response : Response, budget c response) /
        (Fintype.card C : ℚ) ^ 2 := by
      rw [Finset.sum_comm]
      simp only [div_eq_mul_inv, Finset.sum_mul]

end Bcs.TotalOracle
