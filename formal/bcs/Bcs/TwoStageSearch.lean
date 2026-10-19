import Bcs.FootprintCharging
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact probability of a two-stage adaptive search

The parent samples are independent. After viewing every parent sample,
the strategy selects one child row; all child rows consist of independent
fresh samples. This model proves the probability formula without enumerating
the total-oracle space, and without asserting a concrete protocol attack.
-/
namespace Bcs.TwoStageSearch

open Finset Bcs.TotalOracle.Footprint
open scoped Classical

noncomputable def mass {A : Type} [Fintype A] (event : A → Prop) : ℚ :=
  average (fun a => if event a then 1 else 0)

private theorem average_sub_one {A : Type} [Fintype A] [Nonempty A]
    (f : A → ℚ) : average (fun a => 1 - f a) = 1 - average f := by
  have hc : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, sum_sub_distrib, sub_div, hc]

private theorem average_mul_const {A : Type} [Fintype A]
    (f : A → ℚ) (b : ℚ) : average (fun a => f a * b) = average f * b := by
  simp only [average, ← sum_mul]
  ring

private theorem average_prod {A B : Type} [Fintype A] [Fintype B]
    (f : A × B → ℚ) :
    average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul, ← sum_div]
  ring

theorem mass_not {A : Type} [Fintype A] [Nonempty A] (event : A → Prop) :
    mass (fun a => ¬ event a) = 1 - mass event := by
  unfold mass
  rw [← average_sub_one]
  apply congrArg average
  funext a
  by_cases h : event a <;> simp [h]

theorem all_samples_mass {A : Type} [Fintype A] (event : A → Prop) (n : ℕ) :
    mass (fun samples : Fin n → A => ∀ i, event (samples i)) = (mass event) ^ n := by
  classical
  unfold mass average
  rw [div_pow, Fintype.sum_pow]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  congr 1
  apply sum_congr rfl
  intro samples _
  rw [Fintype.prod_boole]
  split_ifs <;> rfl

/-- At least one hit among `n` independent uniform samples. -/
theorem any_sample_mass {A : Type} [Fintype A] [Nonempty A]
    (event : A → Prop) (n : ℕ) :
    mass (fun samples : Fin n → A => ∃ i, event (samples i)) =
      1 - (1 - mass event) ^ n := by
  have hn := mass_not (fun samples : Fin n → A => ∃ i, event (samples i))
  simp only [not_exists] at hn
  rw [all_samples_mass (fun a => ¬ event a) n, mass_not] at hn
  linarith

/-- The child row may be selected after all parent answers are exposed.
Its fresh samples remain uniform, so the two search probabilities multiply. -/
theorem selected_row_search_mass_uniform
    {A B J : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype J] [DecidableEq J]
    (parentEvent : A → Prop) (childEvent : J → B → Prop)
    (childMass : ℚ) (hchildMass : ∀ j, mass (childEvent j) = childMass)
    (R M : ℕ) (select : (Fin R → A) → J) :
    mass (fun p : (Fin R → A) × (J → (Fin M → B)) =>
      (∃ i, parentEvent (p.1 i)) ∧
        (∃ j, childEvent (select p.1) (p.2 (select p.1) j))) =
      (1 - (1 - mass parentEvent) ^ R) *
        (1 - (1 - childMass) ^ M) := by
  classical
  unfold mass
  rw [average_prod]
  have hrow (parents : Fin R → A) :
      average (fun rows : J → (Fin M → B) =>
        if (∃ i, parentEvent (parents i)) ∧
          (∃ j, childEvent (select parents) (rows (select parents) j))
          then (1 : ℚ) else 0) =
        (if (∃ i, parentEvent (parents i)) then (1 : ℚ) else 0) *
          (1 - (1 - childMass) ^ M) := by
    by_cases h : ∃ i, parentEvent (parents i)
    · simp only [h, true_and, if_true, one_mul]
      let f : (Fin M → B) → ℚ := fun row =>
        if ∃ j, childEvent (select parents) (row j) then (1 : ℚ) else 0
      have he := average_eval (A := J) (C := Fin M → B) (select parents) f
      calc
        _ = average (fun rows : J → (Fin M → B) => f (rows (select parents))) := by
          apply congrArg average
          funext rows
          by_cases hc : ∃ j, childEvent (select parents) (rows (select parents) j) <;>
            simp [f, hc]
        _ = average f := he
        _ = mass (fun row : Fin M → B => ∃ j, childEvent (select parents) (row j)) := by
          apply congrArg average
          funext row
          by_cases hc : ∃ j, childEvent (select parents) (row j) <;> simp [f, hc]
        _ = 1 - (1 - childMass) ^ M := by rw [any_sample_mass, hchildMass]
    · simp only [h, false_and, if_false, zero_mul, average_const]
  have hout :
      average (fun parents : Fin R → A => average (fun rows : J → (Fin M → B) =>
        if (∃ i, parentEvent (parents i)) ∧
          (∃ j, childEvent (select parents) (rows (select parents) j))
          then (1 : ℚ) else 0)) =
      average (fun parents : Fin R → A =>
        (if ∃ i, parentEvent (parents i) then (1 : ℚ) else 0) *
          (1 - (1 - childMass) ^ M)) := by
    apply congrArg average
    funext parents
    exact hrow parents
  convert hout.trans ?_ using 1
  · apply congrArg average
    funext parents
    apply congrArg average
    funext rows
    split_ifs <;> rfl
  rw [average_mul_const]
  have hp : (average fun parents : Fin R → A =>
      if ∃ i, parentEvent (parents i) then (1 : ℚ) else 0) =
      mass (fun parents : Fin R → A => ∃ i, parentEvent (parents i)) := by
    apply congrArg average
    funext parents
    split_ifs <;> rfl
  rw [hp]
  rw [any_sample_mass]
  rfl

/-- Constant child events are the special case used for a fixed good set. -/
theorem selected_row_search_mass
    {A B J : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype J] [DecidableEq J]
    (parentEvent : A → Prop) (childEvent : B → Prop)
    (R M : ℕ) (select : (Fin R → A) → J) :
    mass (fun p : (Fin R → A) × (J → (Fin M → B)) =>
      (∃ i, parentEvent (p.1 i)) ∧ (∃ j, childEvent (p.2 (select p.1) j))) =
      (1 - (1 - mass parentEvent) ^ R) *
        (1 - (1 - mass childEvent) ^ M) :=
  selected_row_search_mass_uniform parentEvent (fun _ => childEvent)
    (mass childEvent) (fun _ => rfl) R M select

end Bcs.TwoStageSearch
