import LigeroFamily.Soundness.ProfiledLiftList

/-! Unique row recovery after restricting the committed tableau to the
columns that pass the Ligero proximity response. -/

set_option autoImplicit false

namespace LfzkV1.ResponseDecode125

open Finset LigeroFamily MultiplicativeCode
open scoped Classical

variable {F CheckedMask DirectMask : Type*} [Field F] [DecidableEq F] [Fintype CheckedMask]
variable {r w n nw nq : ℕ}

private noncomputable def rowErrors (S : Finset (Fin n)) (word : Fin n → F)
    (row : EvaluationRow F r w n) : Finset (Fin n) :=
  S.filter fun j => word j ≠ row (codePosition j)

private theorem row_unique (C : MultiplicativeCode F r w n) (S : Finset (Fin n))
    (word : Fin n → F) {g : ℕ} (hsize : C.k + 2*g ≤ S.card)
    (x y : C.base) (hx : (rowErrors S word x.1).card ≤ g)
    (hy : (rowErrors S word y.1).card ≤ g) : x = y := by
  classical
  let errors := rowErrors S word x.1 ∪ rowErrors S word y.1
  have herrors : errors.card ≤ 2*g :=
    (card_union_le _ _).trans (by omega)
  have hcard := card_le_card_sdiff_add_card (s := S) (t := errors)
  obtain ⟨K, hK, hk⟩ := exists_subset_card_eq (show C.k ≤ (S \ errors).card by omega)
  apply Subtype.ext
  apply C.base_unique x.2 y.2 (codePositions K) (by simpa using hk)
  intro p hp
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
  obtain ⟨hS, he⟩ := mem_sdiff.mp (hK hj)
  have good (z : C.base) (hz : rowErrors S word z.1 ⊆ errors) :
      word j = z.1 (codePosition j) := by
    by_contra h
    exact he (hz (mem_filter.mpr ⟨hS, h⟩))
  exact (good x (subset_union_left)).symm.trans (good y subset_union_right)

private noncomputable def finish (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (S : Finset (Fin n)) (g radius : ℕ)
    (rows : Option (SchemeTestedRow CheckedMask nw nq 1) → C.base) :
    Option (SchemeLiftCandidate C oracle radius) := by
  classical
  let errors := CodingTheory.matrixErrorCoordinates (schemeLiftCommittedRows oracle)
      (schemeLiftCandidateRows (rows none).1 (fun index => (rows (some index)).1))
  exact if hclose : errors.card ≤ radius ∧ (errors ∩ S).card ≤ g then
    some ⟨(rows none).1, (fun index => (rows (some index)).1),
      (rows none).2, (fun index => (rows (some index)).2), hclose.1⟩
  else none

/-- The row-decoder specification can be implemented by bounded-distance
Reed–Solomon decoding on the supplied coordinates. The radius check on the
whole matrix is performed after the rows have been recovered. -/
noncomputable def decode (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) (g radius : ℕ) :
    Option (SchemeLiftCandidate C oracle radius) := by
  classical
  let S := schemeProximityAgreement oracle weights response
  exact if C.k + 2*g ≤ S.card then
    if h : ∀ index, ∃ row : C.base,
        (rowErrors S (schemeLiftCommittedRows oracle index) row.1).card ≤ g then
      finish C oracle S g radius (fun index => (h index).choose)
    else none
  else none

theorem decode_eq_some (C : MultiplicativeCode F r w n)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (weights : SchemeTestedRow CheckedMask nw nq 1 → F)
    (response : EvaluationRow F r w n) (g radius : ℕ)
    (candidate : SchemeLiftCandidate C oracle radius)
    (hsize : C.k + 2*g ≤ (schemeProximityAgreement oracle weights response).card)
    (hrem : (candidate.remainingBadColumns weights response).card ≤ g) :
    decode C oracle weights response g radius = some candidate := by
  classical
  let S := schemeProximityAgreement oracle weights response
  let rows : Option (SchemeTestedRow CheckedMask nw nq 1) → C.base
    | none => ⟨candidate.offset, candidate.offset_mem⟩
    | some i => ⟨candidate.row i, candidate.row_mem i⟩
  have hlocal : candidate.badColumns ∩ S = candidate.remainingBadColumns weights response := by
    ext j
    simp [S, schemeProximityAgreement_eq_compl_disagreement,
      SchemeLiftCandidate.remainingBadColumns]
  have hrow index : (rowErrors S (schemeLiftCommittedRows oracle index)
      (rows index).1).card ≤ g := by
    refine (card_le_card ?_).trans hrem
    intro j hj
    obtain ⟨hjS, hjne⟩ := mem_filter.mp hj
    apply mem_sdiff.mpr
    constructor
    · apply mem_filter.mpr
      refine ⟨mem_univ _, index, ?_⟩
      cases index <;> exact hjne
    · intro h
      change j ∈ schemeProximityAgreement oracle weights response at hjS
      rw [schemeProximityAgreement_eq_compl_disagreement] at hjS
      exact (mem_sdiff.mp hjS).2 h
  have he index : ∃ row : C.base,
      (rowErrors S (schemeLiftCommittedRows oracle index) row.1).card ≤ g :=
    ⟨rows index, hrow index⟩
  dsimp only [S] at he
  have hrows : (fun index => (he index).choose) = rows := by
    funext index
    exact row_unique C S _ hsize _ _ (he index).choose_spec (hrow index)
  unfold decode
  simp only [if_pos hsize, dif_pos he]
  rw [hrows]
  unfold finish
  dsimp only [rows]
  have hclose : candidate.badColumns.card ≤ radius ∧
      (candidate.badColumns ∩ schemeProximityAgreement oracle weights response).card ≤ g :=
    ⟨candidate.close, by
      change (candidate.badColumns ∩ S).card ≤ g
      rw [hlocal]
      exact hrem⟩
  dsimp only [SchemeLiftCandidate.badColumns] at hclose
  rw [dif_pos hclose]

end LfzkV1.ResponseDecode125
