import Bcs.TotalOracle
import Mathlib.Logic.Equiv.Prod

/-!
# Two fresh coordinates of a finite random oracle

When a proof is fixed before any transcript-hash query, its last two distinct
hash inputs are fixed coordinates of the total oracle.  Conditional on every
other answer, those two answers are independent uniform draws.  The lemma
below transports an exact accepting-pair count to the total-oracle sample
space.  It does not cover adaptive selection of either hash input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

abbrev AwayFromTwo (x y : Q) := { z : Q // z ≠ x ∧ z ≠ y }

/-- Separate two distinct oracle coordinates from all other answers. -/
def splitTwo (x y : Q) (hxy : x ≠ y) :
    (Q → C) ≃ ((AwayFromTwo x y → C) × (C × C)) where
  toFun H := (fun z => H z.1, (H x, H y))
  invFun p z :=
    if hz : z = x then p.2.1 else
    if hy : z = y then p.2.2 else p.1 ⟨z, hz, hy⟩
  left_inv H := by
    funext z
    by_cases hx : z = x
    · simp [hx]
    · by_cases hy : z = y
      · subst z
        simp [Ne.symm hxy]
      · simp [hx, hy]
  right_inv p := by
    rcases p with ⟨f, ⟨cx, cy⟩⟩
    apply Prod.ext
    · funext z
      simp [z.property.1, z.property.2]
    · apply Prod.ext
      · simp
      · simp [Ne.symm hxy]

/-- Exact rational sum after holding out two distinct oracle answers.  This
version supports the fractional query-cover weights used by the graded
Ligero response-mass certificate. -/
theorem sum_two_fresh_weight (x y : Q) (hxy : x ≠ y)
    (weight : (AwayFromTwo x y → C) → C → C → ℚ) :
    ∑ H : Q → C, weight (fun z => H z.1) (H x) (H y) =
      ∑ off : AwayFromTwo x y → C, ∑ a : C, ∑ b : C,
        weight off a b := by
  classical
  let e := splitTwo (C := C) x y hxy
  calc
    ∑ H : Q → C, weight (fun z => H z.1) (H x) (H y) =
        ∑ p : (AwayFromTwo x y → C) × (C × C),
          weight p.1 p.2.1 p.2.2 := by
            exact Fintype.sum_equiv e _ _ (by intro H; rfl)
    _ = ∑ off : AwayFromTwo x y → C, ∑ a : C, ∑ b : C,
          weight off a b := by
            simp only [Fintype.sum_prod_type]

/-- A weighted accepting-pair bound, with both answers fresh and every
other oracle coordinate fixed, transfers without rounding to the full
uniform-oracle sample space. -/
theorem two_fresh_weight_ratio_le [Nonempty C] (x y : Q) (hxy : x ≠ y)
    (weight : (AwayFromTwo x y → C) → C → C → ℚ)
    (budget : ℚ)
    (hlocal : ∀ off : AwayFromTwo x y → C,
      ∑ a : C, ∑ b : C, weight off a b ≤ budget) :
    (∑ H : Q → C, weight (fun z => H z.1) (H x) (H y)) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      budget / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let Off := AwayFromTwo x y → C
  let e := splitTwo (C := C) x y hxy
  have hcard : (Fintype.card C : ℚ) ^ Fintype.card Q =
      Fintype.card Off * (Fintype.card C : ℚ) ^ 2 := by
    have hn : Fintype.card C ^ Fintype.card Q =
        Fintype.card Off * Fintype.card C ^ 2 := by
      calc
        Fintype.card C ^ Fintype.card Q = Fintype.card (Q → C) := by simp
        _ = Fintype.card (Off × (C × C)) := Fintype.card_congr e
        _ = Fintype.card Off * Fintype.card C ^ 2 := by simp [pow_two]
    exact_mod_cast hn
  have hOff : (0 : ℚ) < Fintype.card Off := by
    exact_mod_cast Fintype.card_pos
  have hC : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  rw [sum_two_fresh_weight x y hxy, hcard]
  rw [div_le_div_iff₀ (mul_pos hOff (pow_pos hC _)) (pow_pos hC _)]
  have hsum :
      (∑ off : Off, ∑ a : C, ∑ b : C, weight off a b) ≤
        Fintype.card Off * budget := by
    calc
      _ ≤ ∑ _off : Off, budget := Finset.sum_le_sum fun off _ => hlocal off
      _ = Fintype.card Off * budget := by simp [mul_comm]
  have hscale := mul_le_mul_of_nonneg_right hsum (le_of_lt (pow_pos hC 2))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale

/-- The child input may depend on the fresh parent answer.  Summing its
weighted pair cost over parent answers retains their average, even though
the child coordinate differs from answer to answer. -/
theorem dependent_second_weight_ratio_le [Nonempty C]
    (x : Q) (y : C → Q) (hxy : ∀ c, x ≠ y c)
    (weight : ∀ c, (AwayFromTwo x (y c) → C) → C → C → ℚ)
    (budget : C → ℚ)
    (hlocal : ∀ c (off : AwayFromTwo x (y c) → C),
      ∑ b : C, weight c off c b ≤ budget c) :
    (∑ H : Q → C,
        weight (H x) (fun z => H z.1) (H x) (H (y (H x)))) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (∑ c : C, budget c) / (Fintype.card C : ℚ) ^ 2 := by
  classical
  have hC : (0 : ℚ) < Fintype.card C := by
    exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q :=
    pow_pos hC _
  have hsplit :
      (∑ H : Q → C,
        weight (H x) (fun z => H z.1) (H x) (H (y (H x)))) =
      ∑ c : C, ∑ H : Q → C,
        if H x = c then weight c (fun z => H z.1) (H x) (H (y c)) else 0 := by
    calc
      _ = ∑ H : Q → C, ∑ c : C,
          if H x = c then weight c (fun z => H z.1) (H x) (H (y c)) else 0 := by
            apply Finset.sum_congr rfl
            intro H _
            simp
      _ = _ := Finset.sum_comm
  rw [hsplit]
  calc
    (∑ c : C, ∑ H : Q → C,
      if H x = c then weight c (fun z => H z.1) (H x) (H (y c)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q =
      ∑ c : C,
        (∑ H : Q → C,
          if H x = c then weight c (fun z => H z.1) (H x) (H (y c)) else 0) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ c : C, budget c / (Fintype.card C : ℚ) ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      exact two_fresh_weight_ratio_le x (y c) (hxy c)
        (fun off a b => if a = c then weight c off a b else 0)
        (budget c) (by
          intro off
          simpa using hlocal c off)
    _ = (∑ c : C, budget c) / (Fintype.card C : ℚ) ^ 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]

/-- An accepting-pair bound conditional on every other oracle answer gives
the same probability bound for two fixed distinct hash inputs. -/
theorem two_fresh_ratio_le [Nonempty C] (x y : Q) (hxy : x ≠ y)
    (bad : (AwayFromTwo x y → C) → C → C → Prop) (m : ℕ)
    (hpair : ∀ off : AwayFromTwo x y → C,
      (univ.filter fun p : C × C => bad off p.1 p.2).card ≤ m) :
    ((univ.filter fun H : Q → C =>
      bad (fun z => H z.1) (H x) (H y)).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (m : ℚ) / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let Off := AwayFromTwo x y → C
  let e := splitTwo (C := C) x y hxy
  have hcount :
      (univ.filter fun H : Q → C =>
        bad (fun z => H z.1) (H x) (H y)).card =
      ∑ off : Off, (univ.filter fun p : C × C => bad off p.1 p.2).card := by
    rw [Finset.card_filter]
    calc
      (∑ H : Q → C, if bad (fun z => H z.1) (H x) (H y) then 1 else 0)
          = ∑ p : Off × (C × C), if bad p.1 p.2.1 p.2.2 then 1 else 0 := by
              exact Fintype.sum_equiv e _ _ (by intro H; rfl)
      _ = ∑ off : Off,
          (univ.filter fun p : C × C => bad off p.1 p.2).card := by
            rw [Fintype.sum_prod_type]
            simp only [Finset.card_filter]
  have hnat :
      (univ.filter fun H : Q → C =>
        bad (fun z => H z.1) (H x) (H y)).card ≤
      m * Fintype.card Off := by
    rw [hcount]
    calc
      (∑ off : Off, (univ.filter fun p : C × C => bad off p.1 p.2).card)
          ≤ ∑ _off : Off, m := Finset.sum_le_sum fun off _ => hpair off
      _ = m * Fintype.card Off := by simp [mul_comm]
  have hcard : Fintype.card C ^ Fintype.card Q =
      Fintype.card Off * (Fintype.card C ^ 2) := by
    calc
      Fintype.card C ^ Fintype.card Q = Fintype.card (Q → C) := by simp
      _ = Fintype.card (Off × (C × C)) := Fintype.card_congr e
      _ = Fintype.card Off * (Fintype.card C ^ 2) := by simp [pow_two]
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hOff : (0 : ℚ) < Fintype.card Off := by exact_mod_cast Fintype.card_pos
  have hcardQ : (Fintype.card C : ℚ) ^ Fintype.card Q =
      Fintype.card Off * (Fintype.card C : ℚ) ^ 2 := by
    exact_mod_cast hcard
  rw [hcardQ]
  rw [div_le_div_iff₀ (mul_pos hOff (pow_pos hC _)) (pow_pos hC _)]
  have hq :
      ((univ.filter fun H : Q → C =>
        bad (fun z => H z.1) (H x) (H y)).card : ℚ) ≤
      m * Fintype.card Off := by exact_mod_cast hnat
  have hscale := mul_le_mul_of_nonneg_right hq (le_of_lt (pow_pos hC 2))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale

/-- The second point may depend on the first answer.  The first point itself
is fixed, and each possible second point must differ from it.  Summing the
pair counts over first answers retains the flat challenge/query envelope. -/
theorem dependent_second_ratio_le [Nonempty C] (x : Q) (y : C → Q)
    (hxy : ∀ c, x ≠ y c)
    (bad : ∀ c, (AwayFromTwo x (y c) → C) → C → C → Prop)
    (m : C → ℕ)
    (hpair : ∀ c (off : AwayFromTwo x (y c) → C),
      (univ.filter fun p : C × C => p.1 = c ∧ bad c off p.1 p.2).card ≤ m c) :
    ((univ.filter fun H : Q → C =>
      bad (H x) (fun z => H z.1) (H x) (H (y (H x)))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      ((∑ c : C, m c : ℕ) : ℚ) / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let A (c : C) : Finset (Q → C) :=
    univ.filter fun H => H x = c ∧
      bad c (fun z => H z.1) (H x) (H (y c))
  have hsub : (univ.filter fun H : Q → C =>
      bad (H x) (fun z => H z.1) (H x) (H (y (H x)))) ⊆
        univ.biUnion A := by
    intro H hH
    apply Finset.mem_biUnion.mpr
    refine ⟨H x, mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨mem_univ _, rfl, (Finset.mem_filter.mp hH).2⟩
  have hcard : (univ.filter fun H : Q → C =>
      bad (H x) (fun z => H z.1) (H x) (H (y (H x)))).card ≤
        ∑ c : C, (A c).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hden : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := pow_pos hC _
  calc
    ((univ.filter fun H : Q → C =>
      bad (H x) (fun z => H z.1) (H x) (H (y (H x)))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q
        ≤ ((∑ c : C, (A c).card : ℕ) : ℚ) /
            (Fintype.card C : ℚ) ^ Fintype.card Q := by
              exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hden)
    _ = ∑ c : C, ((A c).card : ℚ) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            push_cast
            simp only [div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ∑ c : C, (m c : ℚ) / (Fintype.card C : ℚ) ^ 2 := by
          apply Finset.sum_le_sum
          intro c _
          convert
            (two_fresh_ratio_le x (y c) (hxy c)
              (fun off a b => a = c ∧ bad c off a b) (m c)
              (by
                intro off
                apply le_trans (Finset.card_le_card ?_) (hpair c off)
                intro p hp
                simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp)) using 1
          · rfl
          · simp [A]
    _ = ((∑ c : C, m c : ℕ) : ℚ) / (Fintype.card C : ℚ) ^ 2 := by
          push_cast
          simp only [div_eq_mul_inv, Finset.sum_mul]

end Bcs.TotalOracle
