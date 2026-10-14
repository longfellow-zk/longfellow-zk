import CodingTheory.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Basic proximity and row-combination infrastructure

This module supplies proximity definitions, row combinations, and the
finite-dimensional counting facts used by selected-MCA extraction.
-/

namespace CodingTheory

variable {F : Type*} [Field F] [DecidableEq F]
variable {n : ℕ}

/-- A word lies within Hamming radius `e` of some codeword. -/
def WithinRadius (C : LinearCode F n) (e : ℕ) (received : Word F n) : Prop :=
  ∃ codeword, codeword ∈ C ∧ weight (received - codeword) ≤ e

/-- Linear combination of the rows of a finite word matrix. -/
def wordCombination {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (weights : Row → F) : Word F n :=
  ∑ row, weights row • rows row

/-- Standard basis vector selecting one matrix row. -/
def rowBasis {Row : Type*} [DecidableEq Row] (pivot : Row) : Row → F :=
  fun row ↦ if row = pivot then 1 else 0

omit [DecidableEq F] in
theorem wordCombination_apply {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (weights : Row → F) (j : Fin n) :
    wordCombination rows weights j = ∑ row, weights row * rows row j := by
  classical
  unfold wordCombination
  change (Pi.evalAddMonoidHom (fun _ : Fin n ↦ F) j)
      (∑ row, weights row • rows row) = _
  rw [map_sum]
  rfl

omit [DecidableEq F] in
theorem wordCombination_add_smul {Row : Type*} [Fintype Row]
    (rows : Row → Word F n) (first direction : Row → F) (scalar : F) :
    wordCombination rows (first + scalar • direction) =
      wordCombination rows first + scalar • wordCombination rows direction := by
  classical
  funext j
  simp only [wordCombination_apply, Pi.add_apply, Pi.smul_apply]
  simp only [add_mul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

omit [DecidableEq F] in
theorem wordCombination_rowBasis {Row : Type*} [Fintype Row]
    [DecidableEq Row] (rows : Row → Word F n) (pivot : Row) :
    wordCombination rows (rowBasis pivot) = rows pivot := by
  funext coordinate
  rw [wordCombination_apply]
  simp [rowBasis]

private def transverseCoordinates {Row : Type*}
    (direction : Row → F) (pivot : Row) (weights : Row → F) :
    { row : Row // row ≠ pivot } → F :=
  fun row ↦ weights row.1 -
    weights pivot * (direction row.1 / direction pivot)

omit [DecidableEq F] in
/-- A line-wise subsingleton predicate occupies at most one point in every
fiber parallel to a nonzero direction. -/
theorem card_filter_univ_le_pow_of_line_subsingleton
    {Row : Type*} [Fintype Row] [DecidableEq Row] [Fintype F]
    (property : (Row → F) → Prop) [DecidablePred property]
    (direction : Row → F) (hnonzero : direction ≠ 0)
    (hline : ∀ base,
      { scalar : F | property (base + scalar • direction) }.Subsingleton) :
    (Finset.univ.filter property).card ≤
      Fintype.card F ^ (Fintype.card Row - 1) := by
  classical
  obtain ⟨pivot, hpivot⟩ : ∃ row, direction row ≠ 0 := by
    simpa [Function.ne_iff] using hnonzero
  let Other := { row : Row // row ≠ pivot }
  let Good := ↥(Finset.univ.filter property)
  let project : Good → Other → F := fun weights ↦
    transverseCoordinates direction pivot weights.1
  have hprojectInjective : Function.Injective project := by
    intro first second hproject
    let scalar := (first.1 pivot - second.1 pivot) / direction pivot
    have hcoefficients : first.1 = second.1 + scalar • direction := by
      funext row
      by_cases hrow : row = pivot
      · subst row
        dsimp [scalar]
        field_simp [hpivot]
        ring
      · have hcoordinate := congrFun hproject (⟨row, hrow⟩ : Other)
        dsimp [project, transverseCoordinates] at hcoordinate
        dsimp [scalar]
        field_simp [hpivot] at hcoordinate ⊢
        linear_combination hcoordinate
    have hfirstProperty : property first.1 :=
      (Finset.mem_filter.mp first.2).2
    have hsecondProperty : property second.1 :=
      (Finset.mem_filter.mp second.2).2
    have hscalarZero : scalar = 0 :=
      hline second.1 (by simpa [hcoefficients] using hfirstProperty)
        (by simpa using hsecondProperty)
    apply Subtype.ext
    rw [hcoefficients, hscalarZero]
    simp
  calc
    (Finset.univ.filter property).card = Fintype.card Good :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Other → F) :=
      Fintype.card_le_of_injective project hprojectInjective
    _ = Fintype.card F ^ (Fintype.card Row - 1) := by
      simp [Other, Fintype.card_subtype_compl]

/-- Challenges whose affine matrix combination is close to the code. -/
noncomputable def closeCombinationChallenges {Row : Type*}
    [Fintype Row] [DecidableEq Row] [Fintype F]
    (C : LinearCode F n) (e : ℕ)
    (rows : Row → Word F n) (offset : Word F n) : Finset (Row → F) := by
  classical
  exact Finset.univ.filter fun weights ↦
    WithinRadius C e (offset + wordCombination rows weights)

/-- Columns on which at least one row differs from its selected codeword. -/
noncomputable def matrixErrorCoordinates {Row : Type*} [Fintype Row]
    (rows decodedRows : Row → Word F n) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ ∃ row, rows row j ≠ decodedRows row j

/-- Interleaved proximity: all rows have codeword representatives whose union
of error columns has size at most `e`. -/
def InterleavedWithinRadius {Row : Type*} [Fintype Row]
    (C : LinearCode F n) (e : ℕ) (rows : Row → Word F n) : Prop :=
  ∃ decodedRows : Row → Word F n,
    (∀ row, decodedRows row ∈ C) ∧
    (matrixErrorCoordinates rows decodedRows).card ≤ e

end CodingTheory
