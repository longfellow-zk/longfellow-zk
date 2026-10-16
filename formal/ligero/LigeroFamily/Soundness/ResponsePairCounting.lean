import Mathlib.Tactic

/-!
# Adaptive response counting over two finite challenges

A prover may choose a complete response after its first challenge. A low-event
bound uniform in that response and a high-event bound summed over all responses
still give one bound for the challenge/query pair. This lemma uses no protocol
or hash-transcript definitions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LigeroFamily.ResponsePairCounting

open Finset
open scoped Classical

/-- A challenge-adaptive response costs no extra response-list factor when
the high-event estimate counts all responses jointly. -/
theorem adaptive_response_pair_ratio_le
    {C Response : Type*} [Fintype C] [Nonempty C] [Fintype Response]
    (low high : C → Response → C → Prop) (respond : C → Response)
    (lowBudget highBudget : ℚ)
    (hlow : ∀ a response,
      (∑ b : C, if low a response b then (1 : ℚ) else 0) ≤
        Fintype.card C * lowBudget)
    (hhigh : (∑ response : Response, ∑ a : C, ∑ b : C,
      if high a response b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * highBudget) :
    (∑ a : C, ∑ b : C,
      if low a (respond a) b ∨ high a (respond a) b
      then (1 : ℚ) else 0) / (Fintype.card C : ℚ) ^ 2 ≤
        lowBudget + highBudget := by
  let lowMass (a : C) : ℚ :=
    ∑ b : C, if low a (respond a) b then (1 : ℚ) else 0
  let highMass (a : C) (response : Response) : ℚ :=
    ∑ b : C, if high a response b then (1 : ℚ) else 0
  have hlo : (∑ a : C, lowMass a) ≤
      (Fintype.card C : ℚ) ^ 2 * lowBudget := by
    calc
      _ ≤ ∑ _a : C, (Fintype.card C : ℚ) * lowBudget :=
        Finset.sum_le_sum (fun a _ => hlow a (respond a))
      _ = _ := by simp [pow_two]; ring
  have hhi : (∑ a : C, highMass a (respond a)) ≤
      (Fintype.card C : ℚ) ^ 2 * highBudget := by
    calc
      _ ≤ ∑ a : C, ∑ response : Response, highMass a response := by
        apply Finset.sum_le_sum
        intro a _
        have hn : ∀ response : Response, 0 ≤ highMass a response := by
          intro response
          exact Finset.sum_nonneg (fun b _ => by
            split_ifs <;> positivity)
        exact Finset.single_le_sum
          (s := Finset.univ) (f := highMass a)
          (fun response _ => hn response) (Finset.mem_univ (respond a))
      _ = ∑ response : Response, ∑ a : C, highMass a response := by
        rw [Finset.sum_comm]
      _ ≤ _ := hhigh
  have hsplit :
      (∑ a : C, ∑ b : C,
        if low a (respond a) b ∨ high a (respond a) b
        then (1 : ℚ) else 0) ≤
      (∑ a : C, lowMass a) +
        (∑ a : C, highMass a (respond a)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro b _
    by_cases hl : low a (respond a) b <;>
      by_cases hh : high a (respond a) b <;>
      simp [hl, hh]
  have hq : (0 : ℚ) < (Fintype.card C : ℚ) ^ 2 := by positivity
  apply (div_le_iff₀ hq).mpr
  have := add_le_add hlo hhi
  calc
    _ ≤ (∑ a : C, lowMass a) +
      (∑ a : C, highMass a (respond a)) := hsplit
    _ ≤ (Fintype.card C : ℚ) ^ 2 * lowBudget +
      (Fintype.card C : ℚ) ^ 2 * highBudget := this
    _ = (lowBudget + highBudget) *
      (Fintype.card C : ℚ) ^ 2 := by ring

end LigeroFamily.ResponsePairCounting
