import Bcs.FinalQuery
import Bcs.TwoScaleTerminal

/-! Turn a queried-point policy bound into a terminal verifier bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

/-- The verifier's final child lookup accounts for the terminal failure event.
This applies also to a zero-query prover. -/
theorem tree_two_scale_final_ratio_le
    {Q C Out Parent Response : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N)
    (selected : Out → Parent × Response)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (low high : Parent → Response → C → C → Prop)
    (betaLow betaHigh : ℚ)
    (hbetaLow : 0 ≤ betaLow) (hbetaHigh : 0 ≤ betaHigh)
    (hlow : ∀ p r a,
      ∑ b : C, (if low p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C * betaLow)
    (hhigh : ∀ p,
      ∑ r : Response, ∑ a : C, ∑ b : C,
        (if high p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * betaHigh) :
    let failure := fun H : Q → C =>
      let i := selected (tree.run H).1
      low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
      high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    ((univ.filter failure).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (N + 1 : ℕ) * (betaLow + betaHigh) := by
  classical
  let point : Out → Q := fun out => child (selected out).1 (selected out).2
  let extended := appendFinalQuery tree point
  have hbound := tree_two_scale_terminal_ratio_le extended
    parent child hparent hchild hdisjoint low high betaLow betaHigh
    hbetaLow hbetaHigh hlow hhigh
  have hpoint (H : Q → C) :
      (if (let i := selected (tree.run H).1;
            low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
            high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)))
        then (1 : ℚ) else 0) ≤
      ∑ p : Parent, ∑ r : Response,
        ((if child p r ∈ queried extended H ∧
            low p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
    let i := selected (tree.run H).1
    have hmem : child i.1 i.2 ∈ queried extended H :=
      appendFinalQuery_mem tree point H
    have hfirst : firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
        (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither := by
      rw [firstOfTwoOff_eq]
      exact firstOfTwo_ne_neither_of_right_mem _ _ _ _ hmem
    change (if low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
        high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then
        (1 : ℚ) else 0) ≤ _
    let wt : Parent → Response → ℚ := fun p r =>
      (if child p r ∈ queried extended H ∧
          low p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult extended (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
          high p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)
    have hnonneg (p : Parent) (r : Response) :
        (0 : ℚ) ≤
        ((if child p r ∈ queried extended H ∧
            low p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
      split_ifs <;> norm_num
    have hsingle :
        ((if child i.1 i.2 ∈ queried extended H ∧
            low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
            (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
            high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0)) ≤
        ∑ p : Parent, ∑ r : Response,
          ((if child p r ∈ queried extended H ∧
              low p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
          (if firstOfTwoOffResult extended (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
      change wt i.1 i.2 ≤ ∑ p : Parent, ∑ r : Response, wt p r
      calc
        _ ≤ ∑ r : Response, wt i.1 r :=
          Finset.single_le_sum (fun r _ => hnonneg i.1 r) (mem_univ i.2)
        _ ≤ ∑ p : Parent, ∑ r : Response, wt p r := by
          exact Finset.single_le_sum
            (s := univ) (f := fun p : Parent => ∑ r : Response, wt p r)
            (fun p _ => Finset.sum_nonneg (fun r _ => hnonneg p r))
            (mem_univ i.1)
    by_cases hlo : low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    · have hchoice : (1 : ℚ) ≤
        (if low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
        (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
            (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
            high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) := by
          simp only [if_pos hlo]
          split_ifs <;> norm_num
      simpa only [hlo, true_or, ite_true] using hchoice.trans (by
        simpa only [hmem, true_and] using hsingle)
    · by_cases hhi : high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
      · have hchoice : (1 : ℚ) ≤
          (if child i.1 i.2 ∈ queried extended H ∧
              low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
          (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
              (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
              high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) := by
          simp [hlo, hhi, hfirst]
        simpa only [hlo, hhi, false_or, ite_true] using hchoice.trans hsingle
      · simp [i, hlo, hhi]
        exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun r _ => hnonneg p r
  have hq : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := by positivity
  calc
    ((univ.filter (fun H : Q → C =>
        let i := selected (tree.run H).1;
        low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
        high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q
      = (∑ H : Q → C, if (let i := selected (tree.run H).1;
          low i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
          high i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))) then (1 : ℚ) else 0) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
              Nat.cast_zero]
    _ ≤ (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          ((if child p r ∈ queried extended H ∧
              low p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
          (if firstOfTwoOffResult extended (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0))) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun H _ => hpoint H) hq.le
    _ ≤ (N + 1 : ℕ) * (betaLow + betaHigh) := by
      simpa [extended, Nat.add_comm] using hbound

end Bcs.TotalOracle
