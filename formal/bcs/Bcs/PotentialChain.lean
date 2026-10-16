import Bcs.Potential

/-!
# A field-round / Ligero-challenge / Ligero-query potential telescope

The first `u` slots are field rounds.  The next slot draws the Ligero
combination challenge, and the final slot draws the column query.  If a
doomed prefix survives every field slot, its challenge receives potential
`ψ`; an accepted final query receives the residual `1 - ψ`.  A field-round
escape is charged one.  The result is pathwise and makes no probabilistic
or independence assertion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.PotentialChain

open Finset
open scoped Classical

/-- A path whose nonnegative charges pay at one slot, or whose charges at
two distinct slots add to one, pays at least one in total.  This is the
finite-sum bridge between local verifier roles and the potential compiler. -/
theorem one_or_two_slots_pay {I : Type} [Fintype I] [DecidableEq I]
    (charge : I → ℚ) (hnonneg : ∀ i, 0 ≤ charge i)
    (hpay : (∃ i, 1 ≤ charge i) ∨
      ∃ i j, i ≠ j ∧ 1 ≤ charge i + charge j) :
    1 ≤ ∑ i : I, charge i := by
  rcases hpay with ⟨i, hi⟩ | ⟨i, j, hij, hijpay⟩
  · exact le_trans hi (Finset.single_le_sum (fun k _ => hnonneg k)
      (Finset.mem_univ i))
  · have hsubset : ({i, j} : Finset I) ⊆ Finset.univ := Finset.subset_univ _
    have hsmall : ∑ k ∈ ({i, j} : Finset I), charge k ≤ ∑ k : I, charge k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun k _ _ => hnonneg k)
    have hpair : (∑ k ∈ ({i, j} : Finset I), charge k) = charge i + charge j := by
      simp [hij]
    exact le_trans hijpay (hpair ▸ hsmall)

theorem field_escape_before (u : ℕ) (doomed : ℕ → Prop)
    (h0 : doomed 0) (hu : ¬ doomed u) :
    ∃ i < u, doomed i ∧ ¬ doomed (i + 1) := by
  induction u with
  | zero => exact (hu h0).elim
  | succ u ih =>
      by_cases hp : doomed u
      · exact ⟨u, by omega, hp, hu⟩
      · obtain ⟨i, hi, hdi, hnext⟩ := ih hp
        exact ⟨i, by omega, hdi, hnext⟩

/-- The flat terminal-pair partition.  If the challenge cannot remove doom,
an accepting path either first escapes at a field slot or escapes at its
final query.  This form retains the challenge and query as one joint event
for probability counting. -/
theorem field_or_terminal_query (u : ℕ) (doomed : ℕ → Prop)
    (hstart : doomed 0)
    (hchallenge : doomed u → doomed (u + 1))
    (hend : ¬ doomed (u + 2)) :
    (∃ i < u, doomed i ∧ ¬ doomed (i + 1)) ∨
      (doomed (u + 1) ∧ ¬ doomed (u + 2)) := by
  by_cases hu : doomed u
  · exact Or.inr ⟨hchallenge hu, hend⟩
  · exact Or.inl (field_escape_before u doomed hstart hu)

/-- If doom is lost before the terminal pair, a field-round escape already
pays the full unit.  This is the field branch of the graded telescope. -/
theorem field_escape_sum_ge_one (u : ℕ) (doomed : ℕ → Prop)
    (h0 : doomed 0) (hu : ¬ doomed u) :
    1 ≤ ∑ i ∈ range u,
      if doomed i ∧ ¬ doomed (i + 1) then (1 : ℚ) else 0 := by
  obtain ⟨i, hi, hdi, hnext⟩ := field_escape_before u doomed h0 hu
  have hmem : i ∈ range u := Finset.mem_range.mpr hi
  have hterm : (if doomed i ∧ ¬ doomed (i + 1) then (1 : ℚ) else 0) = 1 := by
    simp [hdi, hnext]
  calc
    (1 : ℚ) = if doomed i ∧ ¬ doomed (i + 1) then 1 else 0 := hterm.symm
    _ ≤ ∑ j ∈ range u,
      if doomed j ∧ ¬ doomed (j + 1) then (1 : ℚ) else 0 := by
        exact Finset.single_le_sum
          (f := fun j => if doomed j ∧ ¬ doomed (j + 1) then (1 : ℚ) else 0)
          (fun j _ => by split <;> positivity) hmem

/-- A Boolean doom chain gives a unit charge on the first field escape, or
splits a unit charge between the final two verifier answers.  No threshold
is imposed on the potential value. -/
theorem field_challenge_query_telescope
    (u : ℕ) (doomed : ℕ → Prop)
    (ψ : ℚ) (hψ1 : ψ ≤ 1)
    (hstart : doomed 0)
    (hchallenge : doomed u → doomed (u + 1))
    (hend : ¬ doomed (u + 2)) :
    1 ≤
      (∑ i ∈ range u,
        if doomed i ∧ ¬ doomed (i + 1) then (1 : ℚ) else 0) +
      (if doomed u then ψ else 0) +
      (if doomed (u + 1) ∧ ¬ doomed (u + 2) then 1 - ψ else 0) := by
  classical
  by_cases hu : doomed u
  · have hq : doomed (u + 1) ∧ ¬ doomed (u + 2) :=
      ⟨hchallenge hu, hend⟩
    simp only [if_pos hu, if_pos hq]
    have hfield : 0 ≤ ∑ i ∈ range u,
        if doomed i ∧ ¬ doomed (i + 1) then (1 : ℚ) else 0 := by
      exact Finset.sum_nonneg fun i _ => by split <;> positivity
    linarith
  · obtain ⟨i, hi, hdi, hnext⟩ := field_escape_before u doomed hstart hu
    have hmem : i ∈ range u := Finset.mem_range.mpr hi
    have hterm : (if doomed i ∧ ¬ doomed (i + 1) then (1 : ℚ) else 0) = 1 := by
      simp [hdi, hnext]
    have hfield : 1 ≤ ∑ j ∈ range u,
        if doomed j ∧ ¬ doomed (j + 1) then (1 : ℚ) else 0 := by
      calc
        (1 : ℚ) = if doomed i ∧ ¬ doomed (i + 1) then 1 else 0 := hterm.symm
        _ ≤ ∑ j ∈ range u,
          if doomed j ∧ ¬ doomed (j + 1) then (1 : ℚ) else 0 := by
            exact Finset.single_le_sum
              (f := fun j => if doomed j ∧ ¬ doomed (j + 1) then (1 : ℚ) else 0)
              (fun j _ => by split <;> positivity) hmem
    have hquery : 0 ≤
        (if doomed (u + 1) ∧ ¬ doomed (u + 2) then 1 - ψ else 0) := by
      split <;> linarith
    simp only [if_neg hu, add_zero]
    linarith

end Bcs.PotentialChain
