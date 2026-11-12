import Mathlib.Algebra.Order.BigOperators.Group.Finset
import CodingTheory.Proximity

/-! Counting points on parallel affine lines in a finite vector space. -/

namespace CodingTheory

private def affineTransverseCoordinates
    {F Row : Type*} [Field F]
    (direction : Row → F) (pivot : Row) (weights : Row → F) :
    { row : Row // row ≠ pivot } → F :=
  fun row ↦ weights row.1 -
    weights pivot * (direction row.1 / direction pivot)

/-- A property occupying at most `bound` points on every affine line in one
nonzero direction occupies at most `bound * |F|^(r-1)` points in the ambient
vector space. -/
theorem card_filter_univ_le_mul_pow_of_affine_line_card
    {F Row : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row] [Nonempty Row]
    (property : (Row → F) → Prop) [DecidablePred property]
    (direction : Row → F) (hnonzero : direction ≠ 0) (bound : ℕ)
    (hline : ∀ base,
      (Finset.univ.filter fun scalar : F ↦
        property (base + scalar • direction)).card ≤ bound) :
    (Finset.univ.filter property).card ≤
      bound * Fintype.card F ^ (Fintype.card Row - 1) := by
  obtain ⟨pivot, hpivot⟩ : ∃ row, direction row ≠ 0 := by
    simpa [Function.ne_iff] using hnonzero
  let Other := { row : Row // row ≠ pivot }
  let good : Finset (Row → F) := Finset.univ.filter property
  let project : (Row → F) → Other → F := fun weights ↦
    affineTransverseCoordinates direction pivot weights
  suffices good.card ≤ bound * (Finset.univ : Finset (Other → F)).card by
    simpa [good, Other]
  apply Finset.card_le_mul_card_image_of_maps_to
    (s := good) (t := (Finset.univ : Finset (Other → F)))
    (f := project) (fun _ _ ↦ Finset.mem_univ _) bound
  intro transverse _
  let fiber := good.filter fun weights ↦ project weights = transverse
  change fiber.card ≤ bound
  by_cases hempty : fiber = ∅
  · simp [hempty]
  · obtain ⟨anchor, hanchor⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let scalarOf : (Row → F) → F := fun weights ↦
      (weights pivot - anchor pivot) / direction pivot
    have hrepresentation (weights : Row → F) (hweights : weights ∈ fiber) :
        weights = anchor + scalarOf weights • direction := by
      have hwproject : project weights = transverse :=
        (Finset.mem_filter.mp hweights).2
      have haproject : project anchor = transverse :=
        (Finset.mem_filter.mp hanchor).2
      funext row
      by_cases hrow : row = pivot
      · subst row
        dsimp [scalarOf]
        field_simp [hpivot]
        ring
      · have hcoordinate : project weights ⟨row, hrow⟩ =
            project anchor ⟨row, hrow⟩ := by
          rw [hwproject, haproject]
        dsimp [project, affineTransverseCoordinates, scalarOf] at hcoordinate ⊢
        field_simp [hpivot] at hcoordinate ⊢
        linear_combination hcoordinate
    apply (Finset.card_le_card_of_injOn scalarOf ?_ ?_).trans
      (hline anchor)
    · intro weights hweights
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hrepresentation weights hweights]
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hweights).1).2
    · intro first hfirst second hsecond hequal
      rw [hrepresentation first hfirst, hrepresentation second hsecond, hequal]

end CodingTheory
