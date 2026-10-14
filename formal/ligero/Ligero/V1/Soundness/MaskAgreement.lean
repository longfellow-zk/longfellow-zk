import LigeroFamily.Soundness.Agreement
import LigeroFamily.Soundness.AgreementProfile











namespace Ligero.V1

open LigeroFamily

open CodingTheory
open MultiplicativeCode

variable {F : Type*} [Field F] [DecidableEq F]
variable {r w n : ℕ}

abbrev wordAgreement := @agreementCoordinates

omit [Field F] in
@[simp] theorem mem_wordAgreement (left right : Word F n) (j : Fin n) :
    j ∈ wordAgreement left right ↔ left j = right j := by
  exact mem_agreementCoordinates left right j

/-- The only local algebra needed by both mask proofs. -/
theorem acceptedColumns_subset_residual_union_agreement
    (query residual : Finset (Fin n))
    (actualCore decodedCore claimed mask : Word F n)
    (hlocal : ∀ j ∈ query, claimed j = actualCore j + mask j)
    (hdecoded : ∀ j ∈ query, j ∉ residual → actualCore j = decodedCore j) :
    query ⊆ residual ∪ wordAgreement mask (claimed - decodedCore) := by
  intro j hj
  by_cases hresidual : j ∈ residual
  · exact Finset.mem_union_left _ hresidual
  · apply Finset.mem_union_right
    apply (mem_wordAgreement _ _ _).mpr
    have hcore := hdecoded j hj hresidual
    have hclaim := hlocal j hj
    simp only [Pi.sub_apply]
    rw [hclaim, hcore]
    ring

/-- Agreement with zero is the complement of Hamming support. -/
theorem wordAgreement_zero_eq_compl_support (word : Word F n) :
    wordAgreement word 0 = Finset.univ \ supportOn Finset.univ word := by
  ext j
  simp [wordAgreement, supportOn]

theorem weight_add_agreement_zero (word : Word F n) :
    weight word + (wordAgreement word 0).card = n := by
  rw [weight, wordAgreement_zero_eq_compl_support]
  have hsubset := supportOn_subset (Finset.univ : Finset (Fin n)) word
  rw [Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hcard := Finset.card_le_card hsubset
  simp only [Finset.card_univ, Fintype.card_fin] at hcard ⊢
  omega

/-- Response interpolation gives the response code minimum distance
`n - (2*k - 1)`.  This is the distance parameter used for unchecked masks. -/
theorem responseCode_minimumDistance
    (C : MultiplicativeCode F r w n) :
    HasMinimumDistanceAtLeast C.responseCode (n - (2 * C.k - 1)) := by
  refine {
    distance_le_length := Nat.sub_le _ _
    weight_ge_distance := ?_ }
  intro word hword hnonzero
  obtain ⟨row, hrow, hcodeword⟩ :=
    C.exists_response_row_of_mem_responseCode hword
  have hrowNe : row ≠ 0 := by
    intro hzero
    apply hnonzero
    rw [← hcodeword, hzero]
    rfl
  have hagreement : (wordAgreement (codeword row) 0).card ≤ 2 * C.k - 1 := by
    simpa [wordAgreement, responseAgreement, agreementCoordinates, codeword] using
      responseAgreement_card_le C hrow C.response.zero_mem hrowNe
  have hpartition := weight_add_agreement_zero (codeword row)
  rw [hcodeword] at hpartition
  rw [hcodeword] at hagreement
  omega

variable [Fintype F]

/-- Response-code words agreeing with an arbitrary committed mask target on
at least `a` columns. -/
noncomputable def responseWordsAgreeingAtLeast
    (C : MultiplicativeCode F r w n) (target : Word F n) (a : ℕ) :
    Finset C.responseCode := by
  classical
  exact Finset.univ.filter fun word ↦
    a ≤ (wordAgreement target word.1).card

noncomputable def responseOffsetsAgreeingAtLeast
    (C : MultiplicativeCode F r w n) (target : Word F n) (a : ℕ) :
    Finset (EvaluationRow F r w n) := by
  classical
  exact Finset.univ.filter fun row ↦
    row ∈ C.response ∧ a ≤ (wordAgreement target (codeword row)).card

/-- Global arithmetic labels realized by agreeing response-code offsets. -/
noncomputable def responseLabelsAgreeingAtLeast
    (C : MultiplicativeCode F r w n) (target : Word F n)
    (label : EvaluationRow F r w n → F) (a : ℕ) : Finset F :=
  (responseOffsetsAgreeingAtLeast C target a).image label

omit [DecidableEq F] [Fintype F] in
theorem codeword_injective_on_response
    (C : MultiplicativeCode F r w n) (h2k : 2 * C.k ≤ n) :
    Set.InjOn (codeword : EvaluationRow F r w n → Word F n)
      (C.response : Set (EvaluationRow F r w n)) := by
  intro left hleft right hright heq
  obtain ⟨J, _hsubset, hJcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin n))) (by simpa using h2k)
  apply C.response_unique hleft hright (codePositions (r := r) (w := w) J)
  · simp [hJcard]
  · intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    exact congrFun heq j

theorem responseOffsetsAgreeingAtLeast_card_le_words
    (C : MultiplicativeCode F r w n) (target : Word F n) (a : ℕ)
    (h2k : 2 * C.k ≤ n) :
    (responseOffsetsAgreeingAtLeast C target a).card ≤
      (responseWordsAgreeingAtLeast C target a).card := by
  classical
  let source := responseOffsetsAgreeingAtLeast C target a
  let encodeSource : ↥source → C.responseCode := fun row ↦
    ⟨codeword row.1, C.codeword_mem_responseCode
      (Finset.mem_filter.mp row.2).2.1⟩
  have hinjective : Function.Injective encodeSource := by
    intro left right heq
    apply Subtype.ext
    apply codeword_injective_on_response C h2k
    · exact (Finset.mem_filter.mp left.2).2.1
    · exact (Finset.mem_filter.mp right.2).2.1
    · exact congrArg Subtype.val heq
  let encodeTarget : ↥source →
      ↥(responseWordsAgreeingAtLeast C target a) := fun row ↦
    ⟨encodeSource row, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp row.2).2.2⟩⟩
  have hinjectiveTarget : Function.Injective encodeTarget := by
    intro left right heq
    exact hinjective (congrArg (fun value ↦ value.1) heq)
  calc
    source.card = Fintype.card ↥source := by simp
    _ ≤ Fintype.card ↥(responseWordsAgreeingAtLeast C target a) :=
      Fintype.card_le_of_injective encodeTarget hinjectiveTarget
    _ = (responseWordsAgreeingAtLeast C target a).card := by simp

/-- The list-size bound needed by V1. The target is an
arbitrary committed word: it is intentionally not assumed to lie in the
response code.  Any proved uniform-family bound at agreement `a` applies:
the Johnson count above its threshold, or a Hahn/Delsarte certificate
(`CodingTheory.HahnDelsarte`) below it. -/
theorem responseWordsAgreeingAtLeast_card_le_of_bound
    (C : MultiplicativeCode F r w n) (target : Word F n) (a B : ℕ)
    (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hbound : UniformFamilyBound n a (2 * C.k - 1) B) :
    (responseWordsAgreeingAtLeast C target a).card ≤ B := by
  classical
  let selected := responseWordsAgreeingAtLeast C target a
  let embed : C.responseCode → Unit → Word F n := fun word _ ↦ word.1
  have hinjective : Function.Injective embed := by
    intro left right heq
    apply Subtype.ext
    exact congrFun heq ()
  let candidates : Finset (Unit → Word F n) := selected.image embed
  have hcard : candidates.card = selected.card := by
    exact Finset.card_image_of_injective selected hinjective
  have hcode : ∀ candidate ∈ candidates, ∀ row, candidate row ∈ C.responseCode := by
    intro candidate hcandidate row
    obtain ⟨word, _hword, rfl⟩ := Finset.mem_image.mp hcandidate
    exact word.2
  have hradius : ∀ candidate ∈ candidates,
      (matrixErrorCoordinates (fun _ : Unit ↦ target) candidate).card ≤ n - a := by
    intro candidate hcandidate
    obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp hcandidate
    have hagreement : a ≤ (wordAgreement target word.1).card :=
      (Finset.mem_filter.mp hword).2
    have hmatrix :
        matrixErrorCoordinates (fun _ : Unit ↦ target) (embed word) =
          Finset.univ \ wordAgreement target word.1 := by
      ext j
      simp [matrixErrorCoordinates, embed, wordAgreement]
    rw [hmatrix, Finset.card_sdiff]
    simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  have hbound' : UniformFamilyBound n (n - (n - a)) (n - (n - (2 * C.k - 1))) B := by
    rw [show n - (n - a) = a by omega, show n - (n - (2 * C.k - 1)) = 2 * C.k - 1 by omega]
    exact hbound
  have hlist :=
    CodingTheory.card_le_of_uniformFamilyBound
      C.responseCode (fun _ : Unit ↦ target) candidates
      (responseCode_minimumDistance C) hcode hradius hclose hbound'
  rw [hcard] at hlist
  simpa [selected] using hlist

/-- The Johnson/incidence bound needed by V1. The target is an
arbitrary committed word: it is intentionally not assumed to lie in the
response code. -/
theorem responseWordsAgreeingAtLeast_card_le
    (C : MultiplicativeCode F r w n) (target : Word F n) (a : ℕ)
    (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)) :
    (responseWordsAgreeingAtLeast C target a).card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a :=
  responseWordsAgreeingAtLeast_card_le_of_bound C target a _ ha hclose
    (uncheckedAgreementListBound_uniformFamilyBound n (2 * C.k - 1) a ha hclose hden)

theorem responseOffsetsAgreeingAtLeast_card_le_of_bound
    (C : MultiplicativeCode F r w n) (target : Word F n) (a B : ℕ)
    (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hbound : UniformFamilyBound n a (2 * C.k - 1) B) :
    (responseOffsetsAgreeingAtLeast C target a).card ≤ B :=
  (responseOffsetsAgreeingAtLeast_card_le_words C target a h2k).trans
    (responseWordsAgreeingAtLeast_card_le_of_bound C target a B ha hclose hbound)

theorem responseLabelsAgreeingAtLeast_card_le_of_bound
    (C : MultiplicativeCode F r w n) (target : Word F n)
    (label : EvaluationRow F r w n → F) (a B : ℕ)
    (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hbound : UniformFamilyBound n a (2 * C.k - 1) B) :
    (responseLabelsAgreeingAtLeast C target label a).card ≤ B :=
  (Finset.card_image_le.trans
    (responseOffsetsAgreeingAtLeast_card_le_of_bound C target a B h2k ha hclose hbound))

theorem responseOffsetsAgreeingAtLeast_card_le
    (C : MultiplicativeCode F r w n) (target : Word F n) (a : ℕ)
    (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)) :
    (responseOffsetsAgreeingAtLeast C target a).card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a :=
  (responseOffsetsAgreeingAtLeast_card_le_words C target a h2k).trans
    (responseWordsAgreeingAtLeast_card_le C target a ha hclose hden)

theorem responseLabelsAgreeingAtLeast_card_le
    (C : MultiplicativeCode F r w n) (target : Word F n)
    (label : EvaluationRow F r w n → F) (a : ℕ)
    (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)) :
    (responseLabelsAgreeingAtLeast C target label a).card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a :=
  (Finset.card_image_le.trans
    (responseOffsetsAgreeingAtLeast_card_le C target a h2k ha hclose hden))

end Ligero.V1
