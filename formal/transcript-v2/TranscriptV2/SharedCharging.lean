import TranscriptV2.Charging
import Bcs.FirstPairQuery
import Bcs.TwoFreshCoordinates
import Bcs.PotentialOracle

/-! Shared charging for single-answer frontend failures and Polygero's
two-answer high-response term. The latter is charged at its parent query.
Keeping the actual parent-query count until the final sum avoids charging a
full query budget separately to each protocol. Link feedback supplies the
parent-first condition for an accepted path; it is not assumed for all queries. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P A : Type} [Fintype P] [DecidableEq P] [Fintype A] [Nonempty A]

/-- A child input includes a claimed parent link as well as the protocol
response. Exactly one claimed link matches each parent answer, so summing
over these child inputs does not multiply the protocol's response budget. -/
theorem feedback_sum {Link C Response : Type}
    [Fintype Link] [Fintype C] [Fintype Response]
    (weight : Response → C → C → ℚ) :
    (∑ r : Link × Response, ∑ a : Link × C, ∑ b : Link × C,
      if a.1 = r.1 then weight r.2 a.2 b.2 else 0) =
      (Fintype.card Link : ℚ)^2 * ∑ r : Response, ∑ a : C, ∑ b : C, weight r a b := by
  have hlocal (a b : Link × C) :
      (∑ r : Link × Response, if a.1 = r.1 then weight r.2 a.2 b.2 else 0) =
        ∑ r : Response, weight r a.2 b.2 := by
    simp [Fintype.sum_prod_type, eq_comm]
  calc
    _ = ∑ a : Link × C, ∑ b : Link × C, ∑ r : Link × Response,
        if a.1 = r.1 then weight r.2 a.2 b.2 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
    _ = ∑ a : Link × C, ∑ b : Link × C, ∑ r : Response, weight r a.2 b.2 := by
      simp_rw [hlocal]
    _ = (Fintype.card Link : ℚ)^2 * ∑ a : C, ∑ b : C, ∑ r : Response, weight r a b := by
      simp [Fintype.sum_prod_type, ← mul_sum, pow_two, mul_assoc]
    _ = _ := by
      congr 1
      calc
        _ = ∑ a : C, ∑ r : Response, ∑ b : C, weight r a b :=
          sum_congr rfl (fun _ _ => sum_comm)
        _ = _ := sum_comm

private theorem pair_mean (p c : P) (hne : p ≠ c)
    (weight : (P → A) → A → A → ℚ)
    (hoff : ∀ H H', (∀ z, z ≠ p → z ≠ c → H z = H' z) →
      ∀ a b, weight H a b = weight H' a b) :
    (Fintype.card A : ℚ)^2 * (∑ H : P → A, weight H (H p) (H c)) =
      ∑ H : P → A, ∑ a, ∑ b, weight H a b := by
  let rep := fun off : AwayFromTwo p c → A =>
    (splitTwo (C := A) p c hne).symm
      (off, (Classical.choice inferInstance, Classical.choice inferInstance))
  have hrep (H : P → A) : ∀ z, z ≠ p → z ≠ c → rep (fun z => H z.1) z = H z := by
    intro z hp hc
    simp [rep, splitTwo, hp, hc]
  have hw := sum_two_fresh_weight p c hne (fun off a b => weight (rep off) a b)
  have hm := sum_two_fresh_weight p c hne
    (fun off _ _ => ∑ a, ∑ b, weight (rep off) a b)
  simp_rw [hoff _ _ (hrep _)] at hw hm
  rw [hw, hm]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_sum, pow_two, mul_assoc]

/-- A high-response family retains its cost per queried parent, instead of
prematurely replacing the number of parents by the entire query budget. -/
theorem parent_first_sum_le {Parent Response Out : Type}
    [Fintype Parent] [Fintype Response] {fuel : ℕ}
    (tree : Tree P A Out fuel) (parent : Parent → P) (child : Parent → Response → P)
    (hne : ∀ p r, parent p ≠ child p r)
    (weight : Parent → Response → (P → A) → A → A → ℚ)
    (hoff : ∀ p r H H',
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      ∀ a b, weight p r H a b = weight p r H' a b)
    (hnonneg : ∀ p r H a b, 0 ≤ weight p r H a b)
    (budget : Parent → ℚ)
    (hlocal : ∀ p H, ∑ r, ∑ a, ∑ b, weight p r H a b ≤
      (Fintype.card A : ℚ)^2 * budget p) :
    (∑ H : P → A, ∑ p, ∑ r,
      if firstOfTwo tree H (parent p) (child p r) = .left then
        weight p r H (H (parent p)) (H (child p r)) else 0) ≤
      ∑ H : P → A, ∑ p, if parent p ∈ seen tree H then budget p else 0 := by
  let charged := fun p r H => firstOfTwo tree H (parent p) (child p r) = .left
  have heq p r := pair_mean (parent p) (child p r) (hne p r)
    (fun H a b => if charged p r H then weight p r H a b else 0)
    (by
      intro H H' h a b
      have ho := firstOfTwo_congr_off tree H H' (parent p) (child p r) h
      simp only [charged, ho, hoff p r H H' h])
  have hlocal' p H : (∑ r, ∑ a, ∑ b,
      if charged p r H then weight p r H a b else 0) ≤
      (Fintype.card A : ℚ)^2 * (if parent p ∈ seen tree H then budget p else 0) := by
    by_cases hp : parent p ∈ seen tree H
    · simp only [hp, ite_true]
      apply le_trans _ (hlocal p H)
      exact sum_le_sum (fun r _ => sum_le_sum (fun a _ => sum_le_sum (fun b _ => by
        split_ifs
        · exact le_rfl
        · exact hnonneg p r H a b)))
    · have hn r : ¬ charged p r H := fun h => hp (List.mem_toFinset.mpr
        (firstOfTwo_left_mem tree H (parent p) (child p r) h))
      simp [hn, hp]
  have hsum : (∑ H : P → A, ∑ p : Parent, ∑ r, ∑ a, ∑ b,
      if charged p r H then weight p r H a b else 0) ≤
      ∑ H : P → A, ∑ p : Parent, (Fintype.card A : ℚ)^2 *
        (if parent p ∈ seen tree H then budget p else 0) :=
    sum_le_sum (fun H _ => sum_le_sum (fun p _ => hlocal' p H))
  simp only [← mul_sum] at hsum
  have hreindex : (∑ H : P → A, ∑ p, ∑ r, ∑ a, ∑ b,
      if charged p r H then weight p r H a b else 0) =
      (Fintype.card A : ℚ)^2 * (∑ H : P → A, ∑ p, ∑ r,
        if charged p r H then weight p r H (H (parent p)) (H (child p r)) else 0) := by
    calc
      _ = ∑ p, ∑ r, ∑ H : P → A, ∑ a, ∑ b,
          if charged p r H then weight p r H a b else 0 := by
        rw [sum_comm]; apply sum_congr rfl; intro p _; rw [sum_comm]
      _ = ∑ p, ∑ r, (Fintype.card A : ℚ)^2 * (∑ H : P → A,
          if charged p r H then weight p r H (H (parent p)) (H (child p r)) else 0) := by
        simp_rw [← heq]
      _ = _ := by
        simp only [← mul_sum]
        congr 1
        calc
          _ = ∑ p, ∑ H : P → A, ∑ r,
              if charged p r H then weight p r H (H (parent p)) (H (child p r)) else 0 :=
            sum_congr rfl (fun _ _ => sum_comm)
          _ = _ := sum_comm
  rw [hreindex] at hsum
  exact (mul_le_mul_iff_of_pos_left (by positivity : (0 : ℚ) <
    (Fintype.card A : ℚ)^2)).mp hsum

/-- Single-answer charges also retain the count of the actual queried roles. -/
theorem queried_weight_sum_le {Out : Type} {fuel : ℕ} (tree : Tree P A Out fuel)
    (weight : P → (P → A) → A → ℚ)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, weight p H a = weight p H' a)
    (budget : P → ℚ)
    (hlocal : ∀ p H, ∑ a, weight p H a ≤ Fintype.card A * budget p) :
    (∑ H : P → A, ∑ p ∈ seen tree H, weight p H (H p)) ≤
      ∑ H : P → A, ∑ p ∈ seen tree H, budget p := by
  have heq p := sum_coord_mul_rat p
    (fun H a => if p ∈ seen tree H then weight p H a else 0)
    (by
      intro H H' h a
      have hm : p ∈ seen tree H ↔ p ∈ seen tree H' := by
        simpa only [seen, List.mem_toFinset] using mem_queried_iff tree p h
      simp only [propext hm, hoff p H H' h])
  have hlocal' p H : (∑ a, if p ∈ seen tree H then weight p H a else 0) ≤
      Fintype.card A * (if p ∈ seen tree H then budget p else 0) := by
    by_cases hp : p ∈ seen tree H
    · simpa only [hp, ite_true] using hlocal p H
    · simp [hp]
  have hsum : (∑ H : P → A, ∑ p : P, ∑ a,
      if p ∈ seen tree H then weight p H a else 0) ≤
      ∑ H : P → A, ∑ p : P, Fintype.card A *
        (if p ∈ seen tree H then budget p else 0) :=
    sum_le_sum (fun H _ => sum_le_sum (fun p _ => hlocal' p H))
  have hreindex : (∑ H : P → A, ∑ p : P, ∑ a,
      if p ∈ seen tree H then weight p H a else 0) =
      (∑ H : P → A, ∑ p : P,
        if p ∈ seen tree H then weight p H (H p) else 0) * Fintype.card A := by
    rw [sum_comm]
    simp_rw [← heq]
    rw [← sum_mul, sum_comm]
  rw [hreindex] at hsum
  simp only [← mul_sum] at hsum
  have h : (∑ H : P → A, ∑ p : P,
      if p ∈ seen tree H then weight p H (H p) else 0) ≤
      ∑ H : P → A, ∑ p : P, if p ∈ seen tree H then budget p else 0 := by
    apply (mul_le_mul_iff_of_pos_left (show (0 : ℚ) < Fintype.card A by positivity)).mp
    calc
      _ = (∑ H : P → A, ∑ p : P,
          if p ∈ seen tree H then weight p H (H p) else 0) * Fintype.card A := mul_comm _ _
      _ ≤ _ := hsum
  simpa only [← sum_filter, filter_mem_eq_inter, univ_inter] using h

/-- One budget for frontend, opening, and high-response charges. The local
cost at a parent includes its share of the grouped two-answer term. Thus the
final coefficient is the largest combined cost of one query role, not the
sum of separate whole-protocol coefficients. No round count occurs here. -/
theorem shared_queried_sum_le {Parent Response Out : Type}
    [Fintype Parent] [Fintype Response] {fuel Q : ℕ}
    (tree : Tree P A Out fuel) (hqueries : ∀ H, (seen tree H).card ≤ Q)
    (parent : Parent → P) (child : Parent → Response → P)
    (hne : ∀ p r, parent p ≠ child p r)
    (single : P → (P → A) → A → ℚ)
    (hsingleOff : ∀ p H H', AgreeOff p H H' → ∀ a, single p H a = single p H' a)
    (pair : Parent → Response → (P → A) → A → A → ℚ)
    (hpairOff : ∀ p r H H',
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      ∀ a b, pair p r H a b = pair p r H' a b)
    (hpairNonneg : ∀ p r H a b, 0 ≤ pair p r H a b)
    (singleBudget : P → ℚ) (pairBudget : Parent → ℚ) (epsilon : ℚ)
    (he : 0 ≤ epsilon)
    (hsingle : ∀ p H, ∑ a, single p H a ≤ Fintype.card A * singleBudget p)
    (hpair : ∀ p H, ∑ r, ∑ a, ∑ b, pair p r H a b ≤
      (Fintype.card A : ℚ)^2 * pairBudget p)
    (hpoint : ∀ z, singleBudget z +
      (∑ p, if parent p = z then pairBudget p else 0) ≤ epsilon) :
    (∑ H : P → A,
      ((∑ z ∈ seen tree H, single z H (H z)) +
        ∑ p, ∑ r, if firstOfTwo tree H (parent p) (child p r) = .left then
          pair p r H (H (parent p)) (H (child p r)) else 0)) ≤
      (Q : ℚ) * epsilon * (Fintype.card A : ℚ)^Fintype.card P := by
  have hs := queried_weight_sum_le tree single hsingleOff singleBudget hsingle
  have hp := parent_first_sum_le tree parent child hne pair hpairOff hpairNonneg
    pairBudget hpair
  have htotal (H : P → A) : (∑ z ∈ seen tree H, singleBudget z) +
      (∑ p, if parent p ∈ seen tree H then pairBudget p else 0) ≤ (Q : ℚ) * epsilon := by
    have hpSum : (∑ z ∈ seen tree H, ∑ p, if parent p = z then pairBudget p else 0) =
        ∑ p, if parent p ∈ seen tree H then pairBudget p else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      simp [eq_comm]
    rw [← hpSum, ← sum_add_distrib]
    calc
      _ ≤ ∑ z ∈ seen tree H, epsilon := sum_le_sum (fun z _ => hpoint z)
      _ = ((seen tree H).card : ℚ) * epsilon := by simp
      _ ≤ (Q : ℚ) * epsilon := mul_le_mul_of_nonneg_right (by exact_mod_cast hqueries H) he
  have hsum : (∑ H : P → A,
      ((∑ z ∈ seen tree H, singleBudget z) +
        ∑ p, if parent p ∈ seen tree H then pairBudget p else 0)) ≤
      ∑ _H : P → A, (Q : ℚ) * epsilon := sum_le_sum (fun H _ => htotal H)
  rw [sum_add_distrib] at hsum ⊢
  apply (add_le_add hs hp).trans
  simpa [mul_comm] using hsum

end TranscriptV2
