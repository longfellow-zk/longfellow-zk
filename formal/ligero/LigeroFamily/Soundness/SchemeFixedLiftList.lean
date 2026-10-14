import CodingTheory.ListDecoding.InterleavedJohnson
import LigeroFamily.Soundness.CodewordInjective
import LigeroFamily.Soundness.ProfiledLiftList








namespace LigeroFamily

open CodingTheory
open MultiplicativeCode

variable {F Equations CheckedMask DirectMask : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable {r w n nw nq radius d : ℕ}

namespace SchemeLiftCandidate

variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- The rowwise committed-codeword matrix determines a scheme lift candidate. -/
theorem candidateRows_injective : Function.Injective
    (fun candidate : SchemeLiftCandidate C oracle radius ↦
      schemeLiftCandidateRows candidate.offset candidate.row) := by
  intro first second hmatrix
  apply SchemeLiftCandidate.ext
  · apply C.baseRow_eq_of_codeword_eq first.offset_mem second.offset_mem
    exact congrFun hmatrix none
  · funext index
    apply C.baseRow_eq_of_codeword_eq (first.row_mem index)
      (second.row_mem index)
    exact congrFun hmatrix (some index)

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq CheckedMask] in
/-- The complete fixed list of radius-`radius` scheme candidates satisfies
any independent uniform-family packing bound. -/
theorem univ_card_le_uniformFamilyBound
    (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hradiusDistance : radius < d) {L : ℕ}
    (hfamily : UniformFamilyBound n (n - radius) (n - d) L) :
    (Finset.univ : Finset (SchemeLiftCandidate C oracle radius)).card ≤ L := by
  let matrices : Finset
      (Option (SchemeTestedRow CheckedMask nw nq 1) → Word F n) :=
    Finset.univ.image fun candidate : SchemeLiftCandidate C oracle radius ↦
      schemeLiftCandidateRows candidate.offset candidate.row
  have hmatricesCard : matrices.card =
      (Finset.univ : Finset (SchemeLiftCandidate C oracle radius)).card := by
    change (Finset.univ.image fun candidate : SchemeLiftCandidate C oracle radius ↦
      schemeLiftCandidateRows candidate.offset candidate.row).card = _
    rw [Finset.card_image_of_injective _ candidateRows_injective]
  have hcode (matrix : Option (SchemeTestedRow CheckedMask nw nq 1) → Word F n)
      (hmatrix : matrix ∈ matrices)
      (row : Option (SchemeTestedRow CheckedMask nw nq 1)) :
      matrix row ∈ C.baseCode := by
    obtain ⟨candidate, _hcandidate, rfl⟩ := Finset.mem_image.mp hmatrix
    cases row with
    | none => exact C.codeword_mem_baseCode candidate.offset_mem
    | some index => exact C.codeword_mem_baseCode (candidate.row_mem index)
  have hclose (matrix : Option (SchemeTestedRow CheckedMask nw nq 1) → Word F n)
      (hmatrix : matrix ∈ matrices) :
      (matrixErrorCoordinates (schemeLiftCommittedRows oracle) matrix).card ≤
        radius := by
    obtain ⟨candidate, _hcandidate, rfl⟩ := Finset.mem_image.mp hmatrix
    exact candidate.close
  have hbound :=
    CodingTheory.card_le_of_uniformFamilyBound
      C.baseCode (schemeLiftCommittedRows oracle) matrices hmin hcode hclose
        hradiusDistance hfamily
  rw [hmatricesCard] at hbound
  exact hbound

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq CheckedMask] in
/-- The complete fixed list of radius-`radius` scheme candidates satisfies
the interleaved Johnson cardinality bound. -/
theorem univ_card_le_listBound
    (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hradiusLength : radius ≤ n) (hradiusDistance : radius < d)
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator n d radius) :
    (Finset.univ : Finset (SchemeLiftCandidate C oracle radius)).card ≤
      CodingTheory.InterleavedJohnson.listBound n d radius := by
  exact univ_card_le_uniformFamilyBound C oracle hmin hradiusDistance
    (InterleavedJohnson.uniformFamilyBound_of_denominator_pos hradiusLength
      hradiusDistance hmin.distance_le_length hden)

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq CheckedMask] in
/-- Inside half the minimum distance, the complete fixed interleaved lift
list is a singleton.  This is the genuine unique-decoding argument: it uses
the triangle inequality for the two column-error sets and does not replace a
directional selected-MCA failure theorem. -/
theorem univ_card_le_one_of_two_mul_radius_lt_distance
    (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hunique : 2 * radius < d) :
    (Finset.univ : Finset (SchemeLiftCandidate C oracle radius)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro first second _hfirst _hsecond
  apply candidateRows_injective
  by_contra hne
  have hdistance : d ≤
      (matrixErrorCoordinates
        (schemeLiftCandidateRows first.offset first.row)
        (schemeLiftCandidateRows second.offset second.row)).card :=
    CodingTheory.InterleavedJohnson.matrixErrorCoordinates_card_ge_distance
      C.baseCode hmin
      (fun row ↦ by
        cases row with
        | none => exact C.codeword_mem_baseCode first.offset_mem
        | some index => exact C.codeword_mem_baseCode (first.row_mem index))
      (fun row ↦ by
        cases row with
        | none => exact C.codeword_mem_baseCode second.offset_mem
        | some index => exact C.codeword_mem_baseCode (second.row_mem index))
      hne
  have hsubset :
      matrixErrorCoordinates
          (schemeLiftCandidateRows first.offset first.row)
          (schemeLiftCandidateRows second.offset second.row) ⊆
        matrixErrorCoordinates (schemeLiftCommittedRows oracle)
            (schemeLiftCandidateRows first.offset first.row) ∪
          matrixErrorCoordinates (schemeLiftCommittedRows oracle)
            (schemeLiftCandidateRows second.offset second.row) := by
    intro coordinate hcoordinate
    have hcoordinate' := Finset.mem_filter.mp hcoordinate
    obtain ⟨row, hrow⟩ := hcoordinate'.2
    rw [Finset.mem_union]
    by_cases hfirst :
        schemeLiftCommittedRows oracle row coordinate =
          schemeLiftCandidateRows first.offset first.row row coordinate
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, row, ?_⟩
      intro hsecond
      apply hrow
      exact hfirst.symm.trans hsecond
    · left
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, row, hfirst⟩
  have hcard :
      (matrixErrorCoordinates
        (schemeLiftCandidateRows first.offset first.row)
        (schemeLiftCandidateRows second.offset second.row)).card ≤
        2 * radius := by
    calc
      _ ≤ (matrixErrorCoordinates (schemeLiftCommittedRows oracle)
              (schemeLiftCandidateRows first.offset first.row) ∪
            matrixErrorCoordinates (schemeLiftCommittedRows oracle)
              (schemeLiftCandidateRows second.offset second.row)).card :=
        Finset.card_le_card hsubset
      _ ≤ (matrixErrorCoordinates (schemeLiftCommittedRows oracle)
              (schemeLiftCandidateRows first.offset first.row)).card +
            (matrixErrorCoordinates (schemeLiftCommittedRows oracle)
              (schemeLiftCandidateRows second.offset second.row)).card :=
        Finset.card_union_le _ _
      _ ≤ radius + radius := Nat.add_le_add first.close second.close
      _ = 2 * radius := by omega
  omega

end SchemeLiftCandidate

end LigeroFamily
