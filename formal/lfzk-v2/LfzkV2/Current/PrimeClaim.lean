import LfzkV2.Current.Prime

/-! The dense split claim comes from the compiled sparse input row, as in
`split.rs::split_claim`. Repeated occurrences of a cell add; no uniqueness
assumption on sparse terms is needed. Shared input bits and the remaining
prime cells keep distinct slots. The layer rows are those of the compiler,
read on the native cells: every pad is native. -/
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

/-- The compiled input row evaluates to `t - <w, v>`, so the runtime's
weights are its negated coefficients and its target is its constant. -/
def Claim.split (layers : List (LinearRow Other F)) (input : LinearRow (Shared ⊕ Other) F) :
    Claim Shared Other F where
  layers := layers
  sharedWeights i := -coefficients input (.inl i)
  otherWeights i := -coefficients input (.inr i)
  target := input.constant

theorem Claim.split_residual [Fintype Shared] [Fintype Other] (layers : List (LinearRow Other F))
    (input : LinearRow (Shared ⊕ Other) F) (shared : Shared → F) (other : Other → F) :
    (Claim.split layers input).residual shared other = -input.eval (Sum.elim shared other) := by
  rw [eval_coefficients, Fintype.sum_sum_type]
  simp only [Claim.residual, Claim.split, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
  ring

/-- The compiler's layer rows, with every pad read at its native cell. -/
def nativeLayers {Pad : Type} (cs : Linear.Constraints Pad F) (padCell : Pad → Other) :
    List (LinearRow Other F) :=
  cs.layers.map fun row => ⟨row.constant, mapTerms row.terms padCell⟩

/-- `split_claim` for the actual compiler: the layer rows, then the input
equation. No row-combination challenge is involved. -/
def Claim.ofConstraints {Pad : Type} {nPublic nPrivate : ℕ} (cs : Linear.Constraints Pad F)
    (padCell : Pad → Other) (privateCoordinate : Fin nPrivate → Shared ⊕ Other)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F) :
    Claim Shared Other F :=
  Claim.split (nativeLayers cs padCell)
    (compileInput cs.inputClaim (fun i => .inr (padCell i)) privateCoordinate publicWeights publicInputs
      privateWeights)

/-- All compiled rows hold exactly when the layer rows hold on the native
cells and the split input equation has zero residual. -/
theorem Claim.ofConstraints_iff [Fintype Shared] [Fintype Other] {Pad : Type} {nPublic nPrivate : ℕ}
    (cs : Linear.Constraints Pad F) (padCell : Pad → Other)
    (privateCoordinate : Fin nPrivate → Shared ⊕ Other)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (shared : Shared → F) (other : Other → F) :
    RowsHold (Linear.compile cs (fun i => .inr (padCell i)) privateCoordinate publicWeights
        publicInputs privateWeights) (Sum.elim shared other) ↔
      RowsHold (Claim.ofConstraints cs padCell privateCoordinate publicWeights publicInputs
          privateWeights).layers other ∧
        (Claim.ofConstraints cs padCell privateCoordinate publicWeights publicInputs
          privateWeights).residual shared other = 0 := by
  rw [Claim.ofConstraints, Claim.split_residual, neg_eq_zero]
  simp only [RowsHold, Linear.compile, Claim.split, nativeLayers, List.forall_mem_append,
    List.forall_mem_map, List.forall_mem_singleton]
  have hlayer : ∀ row : PadExpression Pad F,
      (⟨row.constant, mapTerms row.terms (fun i => (Sum.inr (padCell i) : Shared ⊕ Other))⟩ :
        LinearRow (Shared ⊕ Other) F).eval (Sum.elim shared other) =
      (⟨row.constant, mapTerms row.terms padCell⟩ : LinearRow Other F).eval other := by
    intro row
    simp [PadExpression.eval, mapTerms, Function.comp_def]
  simp only [hlayer]

end LfzkV2.Current.Prime
