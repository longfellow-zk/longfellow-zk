import Bcs.RecomputedRbr

/-!
# Expected local budgets on a sequential coin tape

The usual round-by-round count replaces the budget at every prefix by a
uniform maximum.  For a terminal challenge followed by a query, that loses
the flat challenge/query bound.  Here the local budgets are summed over all
tapes instead.  A protocol can put zero cost at its terminal challenge and
the actual number of accepting query answers at the query slot.  The latter
is then averaged over the challenge without assuming a uniform query bound.

This is a sequential-tape lemma.  Using it for a zero-query Fiat–Shamir
prover additionally requires the verifier's distinct hash inputs to realize
the sequential tape, and a protocol-specific escape decomposition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Finset
open scoped Classical

variable {C : Type} [Fintype C] [DecidableEq C]

/-- A prefix-dependent local count, with no maximum over the prefixes. -/
theorem weighted_tape_card_le_total {T : ℕ}
    (P : ∀ i : Fin T, (Fin i.val → C) → C → Prop)
    (wt : ∀ i : Fin T, (Fin i.val → C) → ℕ)
    (hlocal : ∀ i pref,
      (univ.filter fun c : C => P i pref c).card ≤ wt i pref) :
    (univ.filter fun tape : Fin T → C =>
        ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i)).card * Fintype.card C
      ≤ ∑ tape : Fin T → C, ∑ i : Fin T,
          wt i (Sumcheck.extract_prefix tape i) := by
  classical
  have hunion : (univ.filter fun tape : Fin T → C =>
        ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i))
      = univ.biUnion fun i : Fin T =>
          univ.filter fun tape : Fin T → C =>
            P i (Sumcheck.extract_prefix tape i) (tape i) := by
    ext tape
    simp
  rw [hunion]
  calc
    (univ.biUnion fun i : Fin T =>
        univ.filter fun tape : Fin T → C =>
          P i (Sumcheck.extract_prefix tape i) (tape i)).card * Fintype.card C
        ≤ (∑ i : Fin T,
            (univ.filter fun tape : Fin T → C =>
              P i (Sumcheck.extract_prefix tape i) (tape i)).card) *
              Fintype.card C := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ i : Fin T,
          (univ.filter fun tape : Fin T → C =>
            P i (Sumcheck.extract_prefix tape i) (tape i)).card *
              Fintype.card C := by rw [Finset.sum_mul]
    _ ≤ ∑ i : Fin T, ∑ tape : Fin T → C,
          wt i (Sumcheck.extract_prefix tape i) :=
            Finset.sum_le_sum fun i _ => slot_weighted_card_le i (P i) (wt i) (hlocal i)
    _ = ∑ tape : Fin T → C, ∑ i : Fin T,
          wt i (Sumcheck.extract_prefix tape i) := Finset.sum_comm

/-- Probability form of `weighted_tape_card_le_total`.  Its right-hand side
is the average local answer count divided by the coin-alphabet size. -/
theorem weighted_tape_ratio_le_total [Nonempty C] {T : ℕ}
    (E : (Fin T → C) → Prop)
    (P : ∀ i : Fin T, (Fin i.val → C) → C → Prop)
    (hE : ∀ tape, E tape →
      ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i))
    (wt : ∀ i : Fin T, (Fin i.val → C) → ℕ)
    (hlocal : ∀ i pref,
      (univ.filter fun c : C => P i pref c).card ≤ wt i pref) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ T ≤
      ((∑ tape : Fin T → C, ∑ i : Fin T,
          wt i (Sumcheck.extract_prefix tape i) : ℕ) : ℚ) /
        ((Fintype.card C : ℚ) ^ T * Fintype.card C) := by
  classical
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hsub : (univ.filter E).card ≤
      (univ.filter fun tape : Fin T → C =>
        ∃ i, P i (Sumcheck.extract_prefix tape i) (tape i)).card := by
    apply Finset.card_le_card
    intro tape htape
    exact Finset.mem_filter.mpr
      ⟨mem_univ _, hE tape (Finset.mem_filter.mp htape).2⟩
  have hnat := (Nat.mul_le_mul_right (Fintype.card C) hsub).trans
    (weighted_tape_card_le_total P wt hlocal)
  have hq : ((univ.filter E).card : ℚ) * Fintype.card C ≤
      ((∑ tape : Fin T → C, ∑ i : Fin T,
          wt i (Sumcheck.extract_prefix tape i) : ℕ) : ℚ) := by
    exact_mod_cast hnat
  rw [div_le_div_iff₀ (pow_pos hC _) (mul_pos (pow_pos hC _) hC)]
  have hscale := mul_le_mul_of_nonneg_right hq (le_of_lt (pow_pos hC T))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale

/-- The expected-budget form of an existing round-by-round escape proof.
The caller may replace a uniform round budget by a sharper prefix-dependent
one, provided it bounds the same local bad-answer event. -/
theorem RbrCore.ratio_le_average [Nonempty C] {T : ℕ}
    {Accepts : (Fin T → C) → Prop} {Fails : Prop}
    (R : RbrCore C T Accepts Fails)
    (wt : ∀ i : Fin T, (Fin i.val → C) → ℕ)
    (hlocal : ∀ i pref,
      (univ.filter fun c : C => R.bad i pref c).card ≤ wt i pref) :
    ((univ.filter fun tape : Fin T → C => Accepts tape ∧ Fails).card : ℚ) /
        (Fintype.card C : ℚ) ^ T ≤
      ((∑ tape : Fin T → C, ∑ i : Fin T,
          wt i (Sumcheck.extract_prefix tape i) : ℕ) : ℚ) /
        ((Fintype.card C : ℚ) ^ T * Fintype.card C) :=
  by
    convert weighted_tape_ratio_le_total (fun tape => Accepts tape ∧ Fails) R.bad
      (fun tape h => R.escape_of_accepts tape h.1 h.2) wt hlocal using 1
    · congr 1
      congr 1
      apply congrArg Finset.card
      ext tape
      simp

end Bcs
