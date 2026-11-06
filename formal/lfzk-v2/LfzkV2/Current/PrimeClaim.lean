import LfzkV2.Current.Prime

/-! The dense prime handoff claim comes from the batched sparse affine row.
Repeated occurrences of a cell add; no uniqueness assumption on sparse terms
is needed. Shared input bits and the remaining prime cells keep distinct slots. -/
noncomputable section
namespace LfzkV2.Current.Prime
open Finset SumcheckV2
open scoped Classical

variable {F Slot Shared Other : Type} [Field F]

def coefficients (row : LinearRow Slot F) (slot : Slot) : F :=
  (row.terms.map fun term => if term.1 = slot then term.2 else 0).sum

theorem eval_coefficients [Fintype Slot] (row : LinearRow Slot F) (values : Slot → F) :
    row.eval values = row.constant + ∑ i, coefficients row i * values i := by
  rcases row with ⟨constant,terms⟩
  unfold PadExpression.eval coefficients
  congr 1
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
      rw [← ih]
      simp [ite_mul]

def Claim.fromRow (row : LinearRow (Shared ⊕ Other) F) : Claim Shared Other F where
  sharedWeights := coefficients row ∘ Sum.inl
  otherWeights := coefficients row ∘ Sum.inr
  target := -row.constant

theorem Claim.fromRow_residual [Fintype Shared] [Fintype Other]
    (row : LinearRow (Shared ⊕ Other) F) (shared : Shared → F) (other : Other → F) :
    (Claim.fromRow row).residual shared other = row.eval (Sum.elim shared other) := by
  rw [eval_coefficients, Fintype.sum_sum_type]
  simp only [Claim.residual, Claim.fromRow, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    sub_neg_eq_add]
  ring

end LfzkV2.Current.Prime
