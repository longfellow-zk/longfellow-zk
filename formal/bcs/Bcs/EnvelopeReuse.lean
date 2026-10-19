import Bcs.FootprintCharging
import Mathlib.Data.Fin.Tuple.Basic

/-!
# An incoming mean envelope does not imply a no-loss FS compiler

A six-query tree first searches three parent inputs, then searches three
distinct child inputs belonging to the selected parent. All answers are
uniform in `Fin 16`. A fixed parent/child pair succeeds with probability
`1/256`, but adaptive success exceeds `7/256`.

This is a counterexample to a compiler using only the scalar envelope
premises. It is not an instance of the Polygero equations.
-/

namespace Bcs.TotalOracle.EnvelopeReuse

open Finset Merkle.RandomOracle Footprint
open scoped Classical

private theorem average_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℚ) : average (fun a => f (e a)) = average f := by
  unfold average
  rw [Fintype.card_congr e, Fintype.sum_equiv e _ f (fun _ => rfl)]

private theorem average_prod {A B : Type} [Fintype A] [Fintype B]
    (f : A × B → ℚ) :
    average f = average (fun a => average (fun b => f (a, b))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

abbrev Answer := Fin 16
abbrev Slot := Fin 3
abbrev Input := Slot ⊕ (Slot × Slot)

def choose (a b : Answer) : Slot := if a = 0 then 0 else if b = 0 then 1 else 2

/-- Three parent queries followed by three distinct queries in the chosen
parent's child namespace. The final proof is a pair of indices. -/
def search : Tree Input Answer (Slot × Slot) 6 :=
  .query (.inl 0) fun a => .query (.inl 1) fun b => .query (.inl 2) fun _ =>
    let i := choose a b
    .query (.inr (i, 0)) fun x => .query (.inr (i, 1)) fun y =>
      .query (.inr (i, 2)) fun _ => .done (i, choose x y)

def success (H : Input → Answer) (proof : Slot × Slot) : Prop :=
  H (.inl proof.1) = 0 ∧ H (.inr proof) = 0

def found (r : Slot → Answer) : Prop := r 0 = 0 ∨ r 1 = 0 ∨ r 2 = 0

private theorem choose_success (r : Slot → Answer) :
    r (choose (r 0) (r 1)) = 0 ↔ found r := by
  unfold choose found
  split_ifs <;> simp_all

theorem search_success (H : Input → Answer) :
    success H (search.run H).1 ↔
      found (fun i => H (.inl i)) ∧
        found (fun j => H (.inr (choose (H (.inl 0)) (H (.inl 1)), j))) := by
  simp only [success, search, Tree.run_query, Tree.run_done]
  rw [choose_success (fun i => H (.inl i)),
    choose_success (fun j => H (.inr (choose (H (.inl 0)) (H (.inl 1)), j)))]

private def triple : (Slot → Answer) ≃ Answer × Answer × Answer where
  toFun r := (r 0, r 1, r 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

private theorem mean_gate (yes no : ℚ) :
    average (fun a : Answer => if a = 0 then yes else no) = (yes + 15 * no) / 16 := by
  simp [average, Fin.sum_univ_succ]

/-- The scalar conditional envelope: each new child attempt costs `1/16`
if the parent answer is zero, and zero otherwise. -/
def envelope (a : Answer) : ℚ := if a = 0 then 1 / 16 else 0

theorem envelope_nonneg (a : Answer) : 0 ≤ envelope a := by
  unfold envelope
  split_ifs <;> norm_num

theorem envelope_le_one (a : Answer) : envelope a ≤ 1 := by
  unfold envelope
  split_ifs <;> norm_num

theorem fresh_child_mean (a : Answer) :
    average (fun b : Answer => if a = 0 ∧ b = 0 then (1 : ℚ) else 0) = envelope a := by
  by_cases h : a = 0
  · simp only [h, true_and, envelope, if_true]
    rw [mean_gate]
    norm_num
  · simp [h, envelope]

theorem envelope_mean : average envelope = 1 / 256 := by
  unfold envelope
  rw [mean_gate]
  norm_num

theorem fixed_pair_mean :
    average (fun a : Answer => average (fun b : Answer =>
      if a = 0 ∧ b = 0 then (1 : ℚ) else 0)) = 1 / 256 := by
  simp_rw [fresh_child_mean]
  exact envelope_mean

theorem found_mean : average (fun r => if found r then (1 : ℚ) else 0) = 721 / 4096 := by
  have h := average_equiv triple (fun p =>
    if p.1 = 0 ∨ p.2.1 = 0 ∨ p.2.2 = 0 then (1 : ℚ) else 0)
  have hh : average (fun r => if found r then (1 : ℚ) else 0) =
      average (fun p : Answer × Answer × Answer =>
        if p.1 = 0 ∨ p.2.1 = 0 ∨ p.2.2 = 0 then (1 : ℚ) else 0) := by
    convert h using 1
    apply congrArg average
    funext r
    by_cases hr : found r <;> simp_all [found, triple]
  rw [hh, average_prod]
  have hi (a : Answer) :
      average (fun p : Answer × Answer =>
        if a = 0 ∨ p.1 = 0 ∨ p.2 = 0 then (1 : ℚ) else 0) =
        if a = 0 then 1 else (31 : ℚ) / 256 := by
    rw [average_prod]
    by_cases ha : a = 0
    · simp [ha]
    · simp only [ha, false_or, if_false]
      have hb (b : Answer) :
          average (fun c : Answer => if b = 0 ∨ c = 0 then (1 : ℚ) else 0) =
            if b = 0 then 1 else (1 : ℚ) / 16 := by
        by_cases h : b = 0
        · simp [h]
        · simp only [h, false_or, if_false]; rw [mean_gate]; norm_num
      simp_rw [hb]
      rw [mean_gate]
      norm_num
  simp_rw [hi]
  rw [mean_gate]
  norm_num

private def oracleEquiv : (Input → Answer) ≃
    (Slot → Answer) × (Slot → (Slot → Answer)) :=
  (Equiv.sumArrowEquivProdArrow Slot (Slot × Slot) Answer).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.curry Slot Slot Answer))

/-- Exact success probability in the uniform total-oracle model, with the
query bound enforced by `search : Tree ... 6`. -/
theorem adaptive_success_mean :
    average (fun H => if success H (search.run H).1 then (1 : ℚ) else 0) =
      (721 / 4096 : ℚ) ^ 2 := by
  simp_rw [search_success]
  have he := average_equiv oracleEquiv (fun p =>
    if found p.1 ∧ found (p.2 (choose (p.1 0) (p.1 1))) then (1 : ℚ) else 0)
  change average (fun H : Input → Answer => if found (fun i => H (.inl i)) ∧
    found (fun j => H (.inr (choose (H (.inl 0)) (H (.inl 1)), j))) then (1 : ℚ) else 0) = _ at he
  rw [he, average_prod]
  have hi (r : Slot → Answer) :
      average (fun rows : Slot → (Slot → Answer) =>
        if found r ∧ found (rows (choose (r 0) (r 1))) then (1 : ℚ) else 0) =
        (if found r then 1 else 0) * (721 / 4096 : ℚ) := by
    by_cases h : found r
    · simp only [h, true_and, if_true, one_mul]
      exact (average_eval (choose (r 0) (r 1))
        (fun row : Slot → Answer => if found row then (1 : ℚ) else 0)).trans found_mean
    · simp [h]
  simp_rw [hi]
  have hm {A : Type} [Fintype A] (f : A → ℚ) (c : ℚ) :
      average (fun a => f a * c) = average f * c := by
    simp only [average, ← sum_mul]; ring
  rw [hm, found_mean]
  ring

theorem exceeds_no_loss :
    average (fun H => if success H (search.run H).1 then (1 : ℚ) else 0) >
      (6 + 1) * (1 / 256 : ℚ) := by
  rw [adaptive_success_mean]
  norm_num

/-- Even paying all three parent potentials once cannot pay the three
child budgets when exactly one parent has a positive envelope. -/
theorem once_per_parent_insufficient :
    let r : Slot → Answer := ![0, 1, 1]
    3 * envelope (r (choose (r 0) (r 1))) > ∑ i, envelope (r i) := by
  norm_num [choose, envelope, Fin.sum_univ_succ]

end Bcs.TotalOracle.EnvelopeReuse
