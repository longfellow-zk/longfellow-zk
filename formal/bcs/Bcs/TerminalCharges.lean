import Bcs.AffineBlock
import Bcs.FootprintCharging

/-!
# Fractional charges on complete terminal blocks

The footprint may contain a challenge and every response-keyed terminal
query following it.  Its first activation is independent of all those
answers, even when a terminal query preceded the challenge query.
-/

set_option autoImplicit false

namespace Bcs.TotalOracle.Footprint

open Finset AffineBlock Merkle.RandomOracle
open scoped Classical

variable {Q C Out I : Type} [Fintype Q] [DecidableEq Q]
  [Fintype C] [Nonempty C] [Fintype I]

omit [Fintype Q] [Fintype I] [Fintype C] [Nonempty C] in
theorem split_inside_eval (s : Finset Q) (on : Inside s → C) (off : Outside s → C)
    (q : Q) (hq : q ∈ s) : (split s).symm (on, off) q = on ⟨q, hq⟩ := by
  simp [split, Equiv.piEquivPiSubtypeProd, hq]

omit [Fintype Q] [Fintype I] [Fintype C] [Nonempty C] in
theorem split_outside_eval (s : Finset Q) (on : Inside s → C) (off : Outside s → C)
    (q : Q) (hq : q ∉ s) : (split s).symm (on, off) q = off ⟨q, hq⟩ := by
  simp [split, Equiv.piEquivPiSubtypeProd, hq]

omit [Fintype I] in
/-- Resample one held-out coordinate while keeping every other answer. -/
theorem average_resample (q : Q) (wt : (Q → C) → C → ℚ)
    (hoff : ∀ H H', Bcs.TotalOracle.AgreeOff q H H' → ∀ c, wt H c = wt H' c) :
    average (fun H => wt H (H q)) = average (fun c => average (fun H => wt H c)) := by
  have h := Bcs.TotalOracle.sum_coord_mul_rat q wt hoff
  have hc : (Fintype.card C : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh : (Fintype.card (Q → C) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  simp only [← sum_div]
  rw [sum_comm]
  apply (div_eq_div_iff hh hc).mpr
  rw [div_mul_cancel₀ _ hh]
  exact h

omit [Fintype I] in
/-- Two distinct coordinates are independent uniform answers. -/
theorem average_two_eval (a b : Q) (hab : b ≠ a) (f : C → C → ℚ) :
    average (fun H : Q → C => f (H a) (H b)) =
      average (fun c => average (f c)) := by
  rw [average_resample a (fun H c => f c (H b))]
  · congr 1
    funext c
    exact average_eval b (f c)
  · intro H H' ho c
    rw [ho b hab]

omit [Fintype Q] [Fintype C] [Nonempty C] in
/-- Domain-sensitive accounting for first-hit footprint certificates.
This counts calls in the owned domain rather than the tree's ambient fuel. -/
theorem activated_budget_domain_le {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q)
    (support : I → Finset Q) (budget : I → ℚ) (domain : Finset Q)
    (epsilon kappa : ℚ) (hn : ∀ i, 0 ≤ budget i)
    (hq : ∀ q, (∑ i, if q ∈ support i then budget i else 0) ≤
      if q ∈ domain then kappa else 0)
    (hf : ∀ out, (∑ i, if point out ∈ support i then budget i else 0) ≤ epsilon)
    (H : Q → C) :
    (∑ i, if hits (appendFinalQuery tree point) H (support i) then budget i else 0) ≤
      epsilon + queryCost domain tree H * kappa := by
  induction tree with
  | done out =>
      simpa [appendFinalQuery, Tree.bind, hits_weakenAdd, hits, queryCost] using hf out
  | query q next ih =>
      have hs :
          (∑ i, if hits (appendFinalQuery (.query q next) point) H (support i)
            then budget i else 0) ≤
          (∑ i, if q ∈ support i then budget i else 0) +
          ∑ i, if hits (appendFinalQuery (next (H q)) point) H (support i)
            then budget i else 0 := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        by_cases hi : q ∈ support i
        · simp only [appendFinalQuery, Tree.bind, hits, if_pos hi, ↓reduceIte]
          split_ifs <;> linarith [hn i]
        · simp only [appendFinalQuery, Tree.bind, hits, if_neg hi, zero_add]
          exact le_rfl
      refine hs.trans ((add_le_add (hq q) (ih (H q))).trans ?_)
      simp only [queryCost]
      by_cases h : q ∈ domain
      · simp only [h, ↓reduceIte]
        ring_nf
        rfl
      · simp [h]

end Bcs.TotalOracle.Footprint

namespace Bcs.AffineBlock

open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

/-- An ABS compiler for finite, possibly overlapping, whole-block
footprints. The incidence hypotheses, rather than a query-order premise,
are the exact shared-query accounting obligation. -/
theorem oracle_sound_of_footprints
    {Q C Out I : Type} [Fintype Q] [DecidableEq Q]
    [Fintype C] [Nonempty C] [Fintype I]
    (domain : Finset Q) (point : Out → Q)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : I → ℚ) (rate : Rate)
    (hn : ∀ i H, 0 ≤ weight i H) (hb : ∀ i, 0 ≤ budget i)
    (hl : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i)
    (hq : ∀ q, (∑ i, if q ∈ support i then budget i else 0) ≤
      if q ∈ domain then rate.slope else 0)
    (hf : ∀ out, (∑ i, if point out ∈ support i then budget i else 0) ≤ rate.intercept)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ out H, failure out H → 1 ≤
      ∑ i, if point out ∈ support i then weight i H else 0) :
    OracleSound domain failure rate := by
  intro N tree
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  have he := event_le_expected_budget (appendFinalQuery tree point) support weight
    (fun i _ => budget i) (fun H => failure (tree.run H).1 H) hn hl ?_
  · calc
      Bcs.FiniteProbability.density (fun H => failure (tree.run H).1 H) ≤ _ := he
      _ ≤ average (fun H => rate.intercept + queryCost domain tree H * rate.slope) := by
        apply average_mono
        intro H
        exact activated_budget_domain_le tree point support budget domain
          rate.intercept rate.slope hb hq hf H
      _ = rate.intercept + rate.slope * average (queryCost domain tree) := by
        unfold average
        simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_div,
          ← sum_mul]
        have hc : (Fintype.card (Q → C) : ℚ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        field_simp
  · intro H hfail
    apply (hpay _ H hfail).trans
    apply sum_le_sum
    intro i _
    by_cases hi : point (tree.run H).1 ∈ support i
    · have hh := hits_of_mem (appendFinalQuery tree point) H (support i)
        (point (tree.run H).1) (appendFinalQuery_mem tree point H) hi
      simp [hi, hh]
    · simp only [hi, ↓reduceIte]
      split_ifs <;> simp [hn]

end Bcs.AffineBlock

namespace Bcs.TerminalCharges

/-- The baseline's share of an accepting outcome. The zero-density case
is harmless: no accepting outcome exists, and no division is performed. -/
def basePrice (theta r : ℚ) : ℚ := if r ≤ theta then 1 else theta / r

theorem basePrice_nonneg {theta r : ℚ} (ht : 0 ≤ theta) :
    0 ≤ basePrice theta r := by
  unfold basePrice
  split_ifs with h
  · norm_num
  · exact div_nonneg ht ((lt_of_not_ge h).trans_le' ht).le

theorem basePrice_le_one {theta r : ℚ} (ht : 0 ≤ theta) :
    basePrice theta r ≤ 1 := by
  unfold basePrice
  split_ifs with h
  · exact le_rfl
  · have hr : 0 < r := lt_of_le_of_lt ht (lt_of_not_ge h)
    exact (div_le_one hr).mpr (le_of_lt (lt_of_not_ge h))

theorem basePrice_mul_le {theta r : ℚ} (ht : 0 ≤ theta) :
    basePrice theta r * r ≤ theta := by
  unfold basePrice
  split_ifs with h
  · simpa using h
  · have hr : r ≠ 0 := ne_of_gt (lt_of_le_of_lt ht (lt_of_not_ge h))
    rw [div_mul_cancel₀ _ hr]

theorem excessPrice_mul {theta r : ℚ} (ht : 0 ≤ theta) :
    (1 - basePrice theta r) * r = max 0 (r-theta) := by
  unfold basePrice
  split_ifs with h
  · rw [max_eq_left (sub_nonpos.mpr h)]
    ring
  · have hr : r ≠ 0 := ne_of_gt (lt_of_le_of_lt ht (lt_of_not_ge h))
    rw [max_eq_right (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h)))]
    field_simp

theorem basePrice_ge_threshold {theta r : ℚ}
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (hr1 : r ≤ 1) :
    theta ≤ basePrice theta r := by
  unfold basePrice
  split_ifs with h
  · exact ht1
  · have hr : 0 < r := lt_of_le_of_lt ht0 (lt_of_not_ge h)
    exact (le_div_iff₀ hr).mpr (by nlinarith)

open Finset TotalOracle.Footprint AffineBlock
open scoped Classical

/-- Exact averaging of normalized response charges over a complete block.
Terminal keys need only differ from the challenge key: expectation of the
response sum uses their marginals, and does not assume disjoint events. -/
theorem normalized_block_average
    {A C R : Type} [Fintype A] [DecidableEq A] [Fintype C] [Nonempty C] [Fintype R]
    (challenge : A) (terminal : R → A) (ht : ∀ r, terminal r ≠ challenge)
    (theta : ℚ) (hth : 0 ≤ theta)
    (rank : C → Prop) (responses : C → Finset R) (accept : C → R → C → Prop) :
    average (fun H : A → C => if rank (H challenge) then 1-theta else
      ∑ r ∈ responses (H challenge),
        (1-basePrice theta (average (fun c => if accept (H challenge) r c then 1 else 0))) *
          (if accept (H challenge) r (H (terminal r)) then 1 else 0)) =
    average (fun a : C => if rank a then 1-theta else
      ∑ r ∈ responses a, max 0 (average (fun c => if accept a r c then 1 else 0)-theta)) := by
  let f (r : R) (a c : C) : ℚ := if rank a then 0 else
    if r ∈ responses a then
      (1-basePrice theta (average (fun c => if accept a r c then 1 else 0))) *
        (if accept a r c then 1 else 0) else 0
  have he (H : A → C) :
      (if rank (H challenge) then 1-theta else
        ∑ r ∈ responses (H challenge),
          (1-basePrice theta (average (fun c => if accept (H challenge) r c then 1 else 0))) *
            (if accept (H challenge) r (H (terminal r)) then 1 else 0)) =
      (if rank (H challenge) then 1-theta else 0) +
        ∑ r : R, f r (H challenge) (H (terminal r)) := by
    by_cases hr : rank (H challenge) <;> simp [hr, f]
  simp_rw [he]
  rw [average_add, average_eval challenge (fun a => if rank a then 1-theta else 0), average_sum]
  simp_rw [average_two_eval challenge _ (ht _)]
  rw [← average_sum, ← average_add]
  congr 1
  funext a
  by_cases hr : rank a
  · simp [f, hr]
  · simp only [hr, ↓reduceIte, zero_add]
    have hf (r : R) : average (f r a) =
        if r ∈ responses a then
          max 0 (average (fun c => if accept a r c then 1 else 0)-theta) else 0 := by
      by_cases hm : r ∈ responses a
      · simp only [f, hr, hm, ↓reduceIte]
        rw [average_mul, excessPrice_mul hth]
      · simp [f, hr, hm]
    simp_rw [hf]
    exact (sum_filter (s := univ) (p := fun r => r ∈ responses a) _).symm.trans
      (by simp)

end Bcs.TerminalCharges
