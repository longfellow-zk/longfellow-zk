import Bcs.TotalOracle

/-!
# Graded coordinate counting for Fiat–Shamir

A successful oracle can be assigned to one of finitely many disjoint bands.
For each band, the success event may be charged at either of two kinds of
hash point.  The smaller of the two coordinate budgets is sufficient for
that band.  Summing the band budgets retains agreement-dependent information
without multiplying the budgets of two separately ground challenges.

This is a counting kernel.  A protocol instance must prove that every
accepting execution belongs to a band and triggers *both* coordinate events,
with their commitment contexts fixed off the charged coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

theorem graded_card_le
    {Q C Band : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Fintype Band]
    (E : (Q → C) → Prop) (band : (Q → C) → Band)
    (bad₁ bad₂ : Band → Q → (Q → C) → C → Prop)
    (off₁ : ∀ b i (H H' : Q → C), AgreeOff i H H' →
      ∀ c, bad₁ b i H c → bad₁ b i H' c)
    (off₂ : ∀ b i (H H' : Q → C), AgreeOff i H H' →
      ∀ c, bad₂ b i H c → bad₂ b i H' c)
    (wt₁ wt₂ : Band → Q → (Q → C) → ℕ)
    (local₁ : ∀ b i H, (univ.filter fun c : C => bad₁ b i H c).card ≤ wt₁ b i H)
    (local₂ : ∀ b i H, (univ.filter fun c : C => bad₂ b i H c).card ≤ wt₂ b i H)
    (budget₁ budget₂ : Band → ℕ)
    (total₁ : ∀ b H, ∑ i, wt₁ b i H ≤ budget₁ b)
    (total₂ : ∀ b H, ∑ i, wt₂ b i H ≤ budget₂ b)
    (hit₁ : ∀ H, E H → ∃ i, bad₁ (band H) i H (H i))
    (hit₂ : ∀ H, E H → ∃ i, bad₂ (band H) i H (H i)) :
    (univ.filter E).card * Fintype.card C ≤
      (∑ b : Band, min (budget₁ b) (budget₂ b)) *
        Fintype.card C ^ Fintype.card Q := by
  classical
  let slice (b : Band) : Finset (Q → C) :=
    univ.filter fun H => E H ∧ band H = b
  have hpartition : (univ.filter E).card = ∑ b : Band, (slice b).card := by
    calc
      (univ.filter E).card = ∑ H : Q → C, if E H then 1 else 0 := by
        simp only [Finset.card_filter]
      _ = ∑ H : Q → C, ∑ b : Band, if E H ∧ band H = b then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro H _
        by_cases hE : E H
        · simp [hE]
        · simp [hE]
      _ = ∑ b : Band, ∑ H : Q → C,
          if E H ∧ band H = b then 1 else 0 := Finset.sum_comm
      _ = ∑ b : Band, (slice b).card := by
        apply Finset.sum_congr rfl
        intro b _
        simp only [slice, Finset.card_filter]
  have hslice (b : Band) :
      (slice b).card * Fintype.card C ≤
        min (budget₁ b) (budget₂ b) *
          Fintype.card C ^ Fintype.card Q := by
    have hfirst : (slice b).card * Fintype.card C ≤
        budget₁ b * Fintype.card C ^ Fintype.card Q := by
      have hsub : slice b ⊆
          univ.filter fun H : Q → C => ∃ i, bad₁ b i H (H i) := by
        intro H hH
        have hm := (mem_filter.mp hH).2
        exact mem_filter.mpr ⟨mem_univ _, by simpa [hm.2] using hit₁ H hm.1⟩
      exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans
        (card_exists_coord_le (bad₁ b) (off₁ b) (wt₁ b)
          (local₁ b) (budget₁ b) (total₁ b))
    have hsecond : (slice b).card * Fintype.card C ≤
        budget₂ b * Fintype.card C ^ Fintype.card Q := by
      have hsub : slice b ⊆
          univ.filter fun H : Q → C => ∃ i, bad₂ b i H (H i) := by
        intro H hH
        have hm := (mem_filter.mp hH).2
        exact mem_filter.mpr ⟨mem_univ _, by simpa [hm.2] using hit₂ H hm.1⟩
      exact (Nat.mul_le_mul_right _ (Finset.card_le_card hsub)).trans
        (card_exists_coord_le (bad₂ b) (off₂ b) (wt₂ b)
          (local₂ b) (budget₂ b) (total₂ b))
    by_cases h : budget₁ b ≤ budget₂ b
    · simpa [min_eq_left h] using hfirst
    · have h' : budget₂ b ≤ budget₁ b := Nat.le_of_not_ge h
      simpa [min_eq_right h'] using hsecond
  calc
    (univ.filter E).card * Fintype.card C =
        ∑ b : Band, (slice b).card * Fintype.card C := by
      rw [hpartition, Finset.sum_mul]
    _ ≤ ∑ b : Band, min (budget₁ b) (budget₂ b) *
          Fintype.card C ^ Fintype.card Q :=
      Finset.sum_le_sum fun b _ => hslice b
    _ = (∑ b : Band, min (budget₁ b) (budget₂ b)) *
          Fintype.card C ^ Fintype.card Q := by rw [Finset.sum_mul]

/-- The corresponding random-oracle probability bound.  Each band's two
budgets are alternatives for charging the *same* event; they are not
multiplied. -/
theorem graded_ratio_le
    {Q C Band : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Band]
    (E : (Q → C) → Prop) (band : (Q → C) → Band)
    (bad₁ bad₂ : Band → Q → (Q → C) → C → Prop)
    (off₁ : ∀ b i (H H' : Q → C), AgreeOff i H H' →
      ∀ c, bad₁ b i H c → bad₁ b i H' c)
    (off₂ : ∀ b i (H H' : Q → C), AgreeOff i H H' →
      ∀ c, bad₂ b i H c → bad₂ b i H' c)
    (wt₁ wt₂ : Band → Q → (Q → C) → ℕ)
    (local₁ : ∀ b i H, (univ.filter fun c : C => bad₁ b i H c).card ≤ wt₁ b i H)
    (local₂ : ∀ b i H, (univ.filter fun c : C => bad₂ b i H c).card ≤ wt₂ b i H)
    (budget₁ budget₂ : Band → ℕ)
    (total₁ : ∀ b H, ∑ i, wt₁ b i H ≤ budget₁ b)
    (total₂ : ∀ b H, ∑ i, wt₂ b i H ≤ budget₂ b)
    (hit₁ : ∀ H, E H → ∃ i, bad₁ (band H) i H (H i))
    (hit₂ : ∀ H, E H → ∃ i, bad₂ (band H) i H (H i)) :
    ((univ.filter E).card : ℚ) / (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      ((∑ b : Band, min (budget₁ b) (budget₂ b) : ℕ) : ℚ) /
        Fintype.card C := by
  have hC : (0 : ℚ) < (Fintype.card C : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hq : ((univ.filter E).card : ℚ) * (Fintype.card C : ℚ) ≤
      ((∑ b : Band, min (budget₁ b) (budget₂ b) : ℕ) : ℚ) *
        (Fintype.card C : ℚ) ^ Fintype.card Q := by
    exact_mod_cast graded_card_le E band bad₁ bad₂ off₁ off₂ wt₁ wt₂
      local₁ local₂ budget₁ budget₂ total₁ total₂ hit₁ hit₂
  rw [div_le_div_iff₀ (pow_pos hC _) hC]
  exact hq

end Bcs.TotalOracle
