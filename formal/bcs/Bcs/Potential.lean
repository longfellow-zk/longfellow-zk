import Mathlib

/-!
# Signed and positive-increase accounting for transcript potentials

One interactive execution telescopes signed changes, including decreases on
rejection. A prover searching a transcript tree can retain an earlier
favorable prefix, so the Fiat–Shamir compiler charges only positive increases.
The two operators share the same potential and differ only in accounting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.Potential

open Finset

/-- Change in a potential along one execution.  Negative changes contribute
to the interactive telescope. -/
def signedChange (before after : ℚ) : ℚ := after - before

/-- The increase charged to a newly revealed random answer. -/
def increase (before after : ℚ) : ℚ := max 0 (after - before)

theorem signedChange_le_increase (before after : ℚ) :
    signedChange before after ≤ increase before after :=
  le_max_right _ _

/-- Exact telescope along one transcript. -/
theorem signed_trace_eq_sum (T : ℕ) (value : ℕ → ℚ) :
    value T = value 0 +
      ∑ i ∈ range T, signedChange (value i) (value (i + 1)) := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [sum_range_succ]
      simp only [signedChange] at ih ⊢
      linarith

/-- Finite interactive accounting.  The local costs may use cancellation
between positive and negative changes on the one actual transcript. -/
theorem acceptance_card_le_sum_signed_cost
    {Tape : Type} [Fintype Tape] (T : ℕ)
    (accepts : Tape → Prop) [DecidablePred accepts]
    (value : Tape → ℕ → ℚ) (cost : ℕ → ℚ)
    (hzero : ∀ tape, value tape 0 = 0)
    (hfinal_nonneg : ∀ tape, 0 ≤ value tape T)
    (haccept : ∀ tape, accepts tape → 1 ≤ value tape T)
    (hcost : ∀ i < T,
      ∑ tape : Tape, signedChange (value tape i) (value tape (i + 1)) ≤
        cost i) :
    ((univ.filter accepts).card : ℚ) ≤ ∑ i ∈ range T, cost i := by
  classical
  have hpoint (tape : Tape) :
      (if accepts tape then (1 : ℚ) else 0) ≤ value tape T := by
    by_cases ha : accepts tape
    · simpa [ha] using haccept tape ha
    · simpa [ha] using hfinal_nonneg tape
  calc
    ((univ.filter accepts).card : ℚ) =
        ∑ tape : Tape, if accepts tape then (1 : ℚ) else 0 := by
          rw [Finset.natCast_card_filter]
    _ ≤ ∑ tape : Tape, value tape T :=
      Finset.sum_le_sum (fun tape _ => hpoint tape)
    _ = ∑ tape : Tape, ∑ i ∈ range T,
        signedChange (value tape i) (value tape (i + 1)) := by
          apply Finset.sum_congr rfl
          intro tape _
          simpa only [hzero tape, zero_add] using signed_trace_eq_sum T (value tape)
    _ = ∑ i ∈ range T, ∑ tape : Tape,
        signedChange (value tape i) (value tape (i + 1)) := Finset.sum_comm
    _ ≤ ∑ i ∈ range T, cost i :=
      Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_range.mp hi))

theorem increase_nonneg (before after : ℚ) : 0 ≤ increase before after :=
  le_max_left _ _

/-- A new child cannot raise the maximum over explored prefixes by more than
its positive increase from its parent. -/
theorem max_new_le_old_add_increase (parent current next : ℚ)
    (hparent : parent ≤ current) :
    max current next ≤ current + increase parent next := by
  unfold increase
  apply max_le
  · exact le_add_of_nonneg_right (le_max_left _ _)
  · have h : next - parent ≤ max 0 (next - parent) := le_max_right _ _
    linarith

/-- The maximum-over-prefixes argument, independent of how the next prefix
was selected.  In particular, a search may return to an earlier prefix. -/
theorem max_trace_le_sum_increases (T : ℕ)
    (value parent next : ℕ → ℚ)
    (hparent : ∀ i < T, parent i ≤ value i)
    (hstep : ∀ i < T, value (i + 1) = max (value i) (next i)) :
    value T ≤ value 0 + ∑ i ∈ range T, increase (parent i) (next i) := by
  have haux : ∀ j ≤ T,
      value j ≤ value 0 + ∑ i ∈ range j, increase (parent i) (next i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        intro hj
        have hjT : j < T := by omega
        have hp := max_new_le_old_add_increase
          (parent j) (value j) (next j) (hparent j hjT)
        rw [hstep j hjT]
        rw [sum_range_succ]
        have hi := ih (by omega)
        linarith
  exact haux T le_rfl

/-- Finite state-restoration accounting. `value tape i` is the maximum
potential among the prefixes explored after `i` distinct oracle answers.
The parent of the next explored child may be any earlier prefix, including
one chosen adaptively from the tape seen so far. -/
theorem acceptance_card_le_sum_cost
    {Tape : Type} [Fintype Tape] (T : ℕ)
    (accepts : Tape → Prop) [DecidablePred accepts]
    (value parent next : Tape → ℕ → ℚ)
    (cost : ℕ → ℚ)
    (hzero : ∀ tape, value tape 0 = 0)
    (hparent : ∀ tape i, i < T → parent tape i ≤ value tape i)
    (hstep : ∀ tape i, i < T →
      value tape (i + 1) = max (value tape i) (next tape i))
    (haccept : ∀ tape, accepts tape → 1 ≤ value tape T)
    (hcost : ∀ i < T,
      ∑ tape : Tape, increase (parent tape i) (next tape i) ≤ cost i) :
    ((univ.filter accepts).card : ℚ) ≤ ∑ i ∈ range T, cost i := by
  classical
  have hvalue_nonneg (tape : Tape) : 0 ≤ value tape T := by
    have h := max_trace_le_sum_increases T (value tape) (parent tape)
      (next tape) (hparent tape) (hstep tape)
    rw [hzero] at h
    -- The maximum is monotone from zero, independently of the telescope.
    have hmono : ∀ j ≤ T, 0 ≤ value tape j := by
      intro j
      induction j with
      | zero => simp [hzero]
      | succ j ih =>
          intro hj
          rw [hstep tape j (by omega)]
          exact le_trans (ih (by omega)) (le_max_left _ _)
    exact hmono T le_rfl
  have hpoint (tape : Tape) :
      (if accepts tape then (1 : ℚ) else 0) ≤ value tape T := by
    by_cases ha : accepts tape
    · simpa [ha] using haccept tape ha
    · simpa [ha] using hvalue_nonneg tape
  calc
    ((univ.filter accepts).card : ℚ) =
        ∑ tape : Tape, if accepts tape then (1 : ℚ) else 0 := by
          rw [Finset.natCast_card_filter]
    _ ≤ ∑ tape : Tape, value tape T :=
      Finset.sum_le_sum (fun tape _ => hpoint tape)
    _ ≤ ∑ tape : Tape, ∑ i ∈ range T,
        increase (parent tape i) (next tape i) := by
          apply Finset.sum_le_sum
          intro tape _
          simpa [hzero] using max_trace_le_sum_increases T (value tape)
            (parent tape) (next tape) (hparent tape) (hstep tape)
    _ = ∑ i ∈ range T, ∑ tape : Tape,
        increase (parent tape i) (next tape i) := Finset.sum_comm
    _ ≤ ∑ i ∈ range T, cost i :=
      Finset.sum_le_sum (fun i hi => hcost i (Finset.mem_range.mp hi))

end Bcs.Potential
