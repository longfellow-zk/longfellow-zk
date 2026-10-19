import Bcs.FootprintCharging

/-!
# Stopped potentials and a repeated-child renewal barrier

A nonnegative Bellman potential gives a finite-horizon, stopped success
bound. An exposed parent state with repeatable success probability `c`
cannot be charged merely by its one-trial mass: its potential must pay
`c * (1-v)`. The exact two-state rate is `r*c/(r+c)`.

These statements concern an abstract fresh-sample process. They do not
assert that a Polygero commitment realizes either transition probability.
-/
namespace Bcs.StoppedPotential

open Bcs.TotalOracle.Footprint
open scoped Classical

variable {State Coin : Type} [Fintype Coin] [Nonempty Coin]

/-- Success stops the process. Every nonterminal transition consumes one
fresh uniform sample; the transition may inspect the complete current state. -/
noncomputable def stoppedValue (terminal : State → Prop)
    (next : State → Coin → State) : ℕ → State → ℚ
  | 0, s => if terminal s then 1 else 0
  | n + 1, s => if terminal s then 1 else average (fun c =>
      stoppedValue terminal next n (next s c))

private theorem average_add_const (f : Coin → ℚ) (a : ℚ) :
    average (fun c => f c + a) = average f + a := by
  simp only [average, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, add_div]
  have hc : (Fintype.card Coin : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hc]

/-- A state-dependent Bellman inequality pays for arbitrary stopping and
adaptation. The potential includes value one at an already successful state. -/
theorem stoppedValue_le (terminal : State → Prop) (next : State → Coin → State)
    (potential : State → ℚ) (rate : ℚ)
    (hrate : 0 ≤ rate) (hpotential : ∀ s, 0 ≤ potential s)
    (hterminal : ∀ s, terminal s → 1 ≤ potential s)
    (hstep : ∀ s, ¬ terminal s →
      average (fun c => potential (next s c)) ≤ potential s + rate)
    (n : ℕ) (s : State) :
    stoppedValue terminal next n s ≤ potential s + n * rate := by
  induction n generalizing s with
  | zero =>
      by_cases h : terminal s
      · simpa [stoppedValue, h] using hterminal s h
      · simpa [stoppedValue, h] using hpotential s
  | succ n ih =>
      by_cases h : terminal s
      · simp only [stoppedValue, if_pos h]
        exact (hterminal s h).trans (le_add_of_nonneg_right (by positivity))
      · simp only [stoppedValue, if_neg h]
        calc
          _ ≤ average (fun c => potential (next s c) + n * rate) :=
            average_mono (fun c => ih (next s c))
          _ = average (fun c => potential (next s c)) + (n : ℚ) * rate :=
            average_add_const (Coin := Coin) _ _
          _ ≤ (potential s + rate) + (n : ℚ) * rate := by linarith [hstep s h]
          _ = potential s + (n + 1 : ℕ) * rate := by push_cast; ring

/-- A child attempt succeeds with probability `c`, and otherwise returns
to the same exposed-parent state of potential `v`. -/
theorem repeat_child_step_iff (c v rate : ℚ) :
    c + (1 - c) * v ≤ v + rate ↔ c * (1 - v) ≤ rate := by
  constructor <;> intro h <;> nlinarith

/-- A reusable child hazard forces this transformed capacity cost. Thus
an average of capacities is not the parent-query Bellman obligation. -/
theorem repeat_child_potential_lower_bound (c v rate : ℚ) (hc : 0 < c)
    (hchild : c + (1 - c) * v ≤ v + rate) :
    1 - rate / c ≤ v := by
  have he : 1 - rate / c = (c - rate) / c := by field_simp
  rw [he]
  apply (div_le_iff₀ hc).mpr
  have h := (repeat_child_step_iff c v rate).mp hchild
  nlinarith

/-- The least nonnegative potential for a repeatable capacity. Zero
capacity needs no potential; positive capacity pays the transformed cost. -/
noncomputable def repeatPrice (rate c : ℚ) : ℚ :=
  if c = 0 then 0 else max 0 (1 - rate / c)

theorem repeatPrice_nonneg (rate c : ℚ) : 0 ≤ repeatPrice rate c := by
  unfold repeatPrice
  split_ifs
  · rfl
  · exact le_max_left _ _

theorem repeatPrice_le_of_child (c v rate : ℚ) (hc : 0 ≤ c) (hv : 0 ≤ v)
    (hchild : c + (1 - c) * v ≤ v + rate) :
    repeatPrice rate c ≤ v := by
  by_cases hz : c = 0
  · simpa [repeatPrice, hz] using hv
  · simp only [repeatPrice, if_neg hz]
    exact max_le hv (repeat_child_potential_lower_bound c v rate
      (lt_of_le_of_ne hc (Ne.symm hz)) hchild)

/-- The transformed price itself pays the repeatable child transition. -/
theorem repeatPrice_child_step (c rate : ℚ) (hc : 0 ≤ c) (hrate : 0 ≤ rate) :
    c + (1 - c) * repeatPrice rate c ≤ repeatPrice rate c + rate := by
  by_cases hz : c = 0
  · simpa [repeatPrice, hz] using hrate
  · apply (repeat_child_step_iff _ _ _).mpr
    have hlower : 1 - rate / c ≤ repeatPrice rate c := by
      simp only [repeatPrice, if_neg hz]
      exact le_max_right _ _
    have hcancel : c * (rate / c) = rate := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlower hc
    nlinarith

/-- The correct parent-query necessary inequality for a family of exposed
repeatable capacities is the average transformed price, not their average
one-trial mass. -/
theorem average_repeatPrice_le {A : Type} [Fintype A]
    (capacity potential : A → ℚ) (rate : ℚ)
    (hc : ∀ a, 0 ≤ capacity a) (hv : ∀ a, 0 ≤ potential a)
    (hchild : ∀ a, capacity a + (1 - capacity a) * potential a ≤ potential a + rate)
    (hroot : average potential ≤ rate) :
    average (fun a => repeatPrice rate (capacity a)) ≤ rate := by
  exact (average_mono (fun a => repeatPrice_le_of_child
    (capacity a) (potential a) rate (hc a) (hv a) (hchild a))).trans hroot

/-- Retaining the best previously exposed parent is also paid by the
transformed mean. This is the root-query Bellman step for adaptive search. -/
theorem fresh_parent_best_step {A : Type} [Fintype A] [Nonempty A]
    (capacity : A → ℚ) (rate current : ℚ) (hcurrent : 0 ≤ current)
    (hroot : average (fun a => repeatPrice rate (capacity a)) ≤ rate) :
    average (fun a => max current (repeatPrice rate (capacity a))) ≤ current + rate := by
  calc
    _ ≤ average (fun a => repeatPrice rate (capacity a) + current) := by
      apply average_mono
      intro a
      apply max_le
      · linarith [repeatPrice_nonneg rate (capacity a)]
      · linarith
    _ = average (fun a => repeatPrice rate (capacity a)) + current :=
      average_add_const (Coin := A) _ _
    _ ≤ current + rate := by linarith

/-- The root attempt reaches a usable parent with probability `r`. Any
Bellman certificate that charges root and repeatable child queries at the
same rate must pay at least this harmonic rate. -/
theorem renewal_rate_lower_bound (r c v rate : ℚ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hsum : 0 < r + c)
    (hroot : r * v ≤ rate)
    (hchild : c + (1 - c) * v ≤ v + rate) :
    r * c / (r + c) ≤ rate := by
  apply (div_le_iff₀ hsum).mpr
  have h₁ := mul_le_mul_of_nonneg_left hroot hc
  have h₂ := mul_le_mul_of_nonneg_left
    ((repeat_child_step_iff c v rate).mp hchild) hr
  nlinarith

/-- The lower bound is attained, so it is the exact rate for this
two-state Bellman model. -/
theorem renewal_rate_attained (r c : ℚ) (hsum : r + c ≠ 0) :
    r * (c / (r + c)) = r * c / (r + c) ∧
    c + (1 - c) * (c / (r + c)) = c / (r + c) + r * c / (r + c) := by
  constructor
  · ring
  · field_simp [hsum]
    ring

theorem renewal_potential_bounds (r c : ℚ)
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hsum : 0 < r + c) :
    0 ≤ c / (r + c) ∧ c / (r + c) ≤ 1 := by
  constructor
  · exact div_nonneg hc hsum.le
  · apply (div_le_one hsum).mpr
    linarith

/-- Closed form when a parent has `L` disjoint exceptional types, each of
mass `1/q`, all with repeatable child hazard `c`. -/
theorem rare_type_rate (q L c : ℚ) (hq : 0 < q) (hL : 0 < L) (hc : 0 ≤ c) :
    (L / q) * c / (L / q + c) = L * c / (L + q * c) := by
  have hd : L + q * c ≠ 0 := ne_of_gt (by positivity)
  have he : L / q + c ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- For three or more exceptional types, a child success probability
large compared with `1/q` defeats the proposed rate `2/q` in this model. -/
theorem rare_type_rate_exceeds_two (q L c : ℚ)
    (hq : 0 < q) (hL : 0 < L) (hc : 0 ≤ c)
    (hgap : 2 * L < q * c * (L - 2)) :
    2 / q < (L / q) * c / (L / q + c) := by
  rw [rare_type_rate q L c hq hL hc]
  apply (div_lt_div_iff₀ hq (show 0 < L + q * c by positivity)).mpr
  nlinarith

/-- Three exceptional parent types, each of probability `1/128`, and a
repeatable child hazard `1/3` have one-trial mean `1/128`. Nevertheless
they cannot have Bellman rate `2/128`. This is an abstract obstruction,
not a Polygero attack. -/
theorem small_scalar_mean_counterexample :
    (3 / 128 : ℚ) * (1 / 3) = 1 / 128 ∧
    ¬ ∃ v : ℚ,
      (3 / 128 : ℚ) * v ≤ 2 / 128 ∧
      (1 / 3 : ℚ) + (1 - 1 / 3) * v ≤ v + 2 / 128 := by
  constructor
  · norm_num
  · rintro ⟨v, hroot, hchild⟩
    have h := renewal_rate_lower_bound (3/128) (1/3) v (2/128)
      (by norm_num) (by norm_num) (by norm_num) hroot hchild
    norm_num at h

end Bcs.StoppedPotential
