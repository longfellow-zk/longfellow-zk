import LigeroFamily.Soundness.ProfiledLiftList
import Ligero.V1.Soundness.MaskAgreement
import Ligero.V1.Protocol.Protocol

/-!
# V1 arithmetic responses after a common lift

These lemmas instantiate the shared-column argument against the actual
V1 verifier. The canonical response is formed only from the decoded
core.  The committed direct mask is an arbitrary target word; no code
membership assumption is made about it.
-/

namespace Ligero.V1

open LigeroFamily

open CodingTheory
open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations]
variable {r w n nw nq radius : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : Oracle F nw nq n 1}

namespace SchemeLiftCandidate

noncomputable def v1LinearCanonical
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) : EvaluationRow F r w n :=
  Verifier.linearCore C statement weights fun block row ↦
    candidate.row (Sum.inl ⟨block, row⟩)

noncomputable def v1QuadraticCanonical
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) : EvaluationRow F r w n :=
  Verifier.quadraticCore weights fun block row ↦
    candidate.row (Sum.inl ⟨block, row⟩)

abbrev v1Messages (candidate : SchemeLiftCandidate C oracle radius) :=
  candidate.decodedMessages

abbrev v1LinearResidual (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations) :=
  candidate.linearResidual statement

abbrev v1QuadraticResidual (candidate : SchemeLiftCandidate C oracle radius) :=
  candidate.quadraticResidual

omit [Fintype F] in
theorem v1LinearCanonical_witness
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (i : Fin w) :
    v1LinearCanonical candidate statement weights (witnessPosition i) =
      ∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
        statement.A weights block row i *
          v1Messages candidate block row i := by
  simp [v1LinearCanonical, v1Messages,
    LigeroFamily.SchemeLiftCandidate.decodedMessages,
    LigeroFamily.SchemeLiftCandidate.decodedCore,
    Verifier.linearCore, rowMul, Verifier.coefficientRow, witnessValues]

omit [Fintype F] in
theorem v1LinearCanonical_sum
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) :
    (∑ i : Fin w,
      v1LinearCanonical candidate statement weights (witnessPosition i)) =
      ∑ equation : Equations, weights equation *
        statement.linearValue (v1Messages candidate) equation := by
  rw [show (∑ i : Fin w,
      v1LinearCanonical candidate statement weights (witnessPosition i)) =
      ∑ i : Fin w, ∑ block : CoreBlock,
        ∑ row : Fin (block.rowCount nw nq),
          statement.A weights block row i *
            v1Messages candidate block row i by
        apply Finset.sum_congr rfl
        intro i _
        exact v1LinearCanonical_witness candidate statement weights i]
  simp only [ConstraintSystem.A, ConstraintSystem.linearValue,
    Finset.mul_sum, Finset.sum_mul]
  let summand : (Fin w × CoreRow nw nq) → Equations → F :=
    fun index equation ↦ weights equation *
      statement.coefficient equation index.2.1 index.2.2 index.1 *
        v1Messages candidate index.2.1 index.2.2 index.1
  calc
    _ = ∑ index : Fin w × CoreRow nw nq,
        ∑ equation : Equations, summand index equation := by
      simp [summand, Fintype.sum_prod_type, Fintype.sum_sigma, mul_assoc]
    _ = ∑ equation : Equations,
        ∑ index : Fin w × CoreRow nw nq, summand index equation :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro equation _
      calc
        (∑ index : Fin w × CoreRow nw nq, summand index equation) =
            ∑ i : Fin w, ∑ blockRow : CoreRow nw nq,
              weights equation *
                statement.coefficient equation blockRow.1 blockRow.2 i *
                  v1Messages candidate blockRow.1 blockRow.2 i := by
          simp [summand, Fintype.sum_prod_type]
        _ = ∑ blockRow : CoreRow nw nq, ∑ i : Fin w,
              weights equation *
                statement.coefficient equation blockRow.1 blockRow.2 i *
                  v1Messages candidate blockRow.1 blockRow.2 i :=
          Finset.sum_comm
        _ = _ := by simp [Fintype.sum_sigma, mul_assoc]

omit [Fintype F] in
theorem v1_linear_offset_label
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (hglobal : (∑ i : Fin w, claimed (witnessPosition i)) =
      statement.combinedTarget weights) :
    -(∑ i : Fin w,
        (claimed - v1LinearCanonical candidate statement weights)
          (witnessPosition i)) =
      finiteDot weights (v1LinearResidual candidate statement) := by
  rw [show (∑ i : Fin w,
      (claimed - v1LinearCanonical candidate statement weights)
        (witnessPosition i)) =
      (∑ i : Fin w, claimed (witnessPosition i)) -
        ∑ i : Fin w,
          v1LinearCanonical candidate statement weights
            (witnessPosition i) by
      simp [Finset.sum_sub_distrib]]
  rw [hglobal, v1LinearCanonical_sum candidate statement weights]
  unfold ConstraintSystem.combinedTarget finiteDot v1LinearResidual
    LigeroFamily.SchemeLiftCandidate.linearResidual
    v1Messages
    LigeroFamily.SchemeLiftCandidate.decodedMessages
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

omit [Fintype F] [Fintype Equations] in
theorem v1QuadraticCanonical_witness
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) (i : Fin w) :
    v1QuadraticCanonical candidate weights (witnessPosition i) =
      finiteDot weights (fun row ↦ v1QuadraticResidual candidate row i) := by
  simp [v1QuadraticCanonical, v1QuadraticResidual,
    LigeroFamily.SchemeLiftCandidate.quadraticResidual,
    LigeroFamily.SchemeLiftCandidate.decodedMessages,
    LigeroFamily.SchemeLiftCandidate.decodedCore, Verifier.quadraticCore,
    finiteDot, rowMul, witnessValues]

omit [Fintype F] [Fintype Equations] in
theorem v1_quadratic_offset_label
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) (i : Fin w) (claimed : EvaluationRow F r w n)
    (hglobal : claimed (witnessPosition i) = 0) :
    -(claimed - v1QuadraticCanonical candidate weights)
        (witnessPosition i) =
      finiteDot weights (fun row ↦ v1QuadraticResidual candidate row i) := by
  simp only [Pi.sub_apply, hglobal, zero_sub, neg_neg]
  exact v1QuadraticCanonical_witness candidate weights i

omit [Fintype F] in
theorem v1LinearCanonical_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) :
    v1LinearCanonical candidate statement weights ∈ C.response := by
  unfold v1LinearCanonical Verifier.linearCore
  apply Submodule.sum_mem
  intro block _
  apply Submodule.sum_mem
  intro row _
  exact C.mul_mem (C.encode_mem 0 (statement.A weights block row))
    (candidate.row_mem (Sum.inl ⟨block, row⟩))

omit [Fintype F] [Fintype Equations] in
theorem v1QuadraticCanonical_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) :
    v1QuadraticCanonical candidate weights ∈ C.response := by
  unfold v1QuadraticCanonical Verifier.quadraticCore
  apply Submodule.sum_mem
  intro row _
  apply C.response.smul_mem
  apply C.response.sub_mem
  · exact C.mul_mem
      (candidate.row_mem (Sum.inl ⟨CoreBlock.left, row⟩))
      (candidate.row_mem (Sum.inl ⟨CoreBlock.right, row⟩))
  · exact C.base_le_response
      (candidate.row_mem (Sum.inl ⟨CoreBlock.output, row⟩))

/- Accepted linear labels inject into the Johnson-bounded set of agreeing
response offsets. -/
theorem v1_linear_label_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (haccept : claimed ∈ C.response ∧
      (∑ i : Fin w, claimed (witnessPosition i)) =
        statement.combinedTarget weights)
    (a : ℕ)
    (hagreement : a ≤ (wordAgreement (oracle.directMask 0 .linear)
      (codeword (claimed - v1LinearCanonical candidate statement weights))).card) :
    finiteDot weights (v1LinearResidual candidate statement) ∈
      responseLabelsAgreeingAtLeast C (oracle.directMask 0 .linear)
        (fun row ↦ -(∑ i : Fin w, row (witnessPosition i))) a := by
  classical
  apply Finset.mem_image.mpr
  let offset := claimed - v1LinearCanonical candidate statement weights
  have hoffset : offset ∈ C.response := C.response.sub_mem haccept.1
    (v1LinearCanonical_mem candidate statement weights)
  refine ⟨offset, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hoffset, hagreement⟩, ?_⟩
  exact v1_linear_offset_label candidate statement weights claimed
    haccept.2

/-- The same incidence bridge for a selected violated quadratic coordinate. -/
theorem v1_quadratic_label_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) (i : Fin w) (claimed : EvaluationRow F r w n)
    (haccept : claimed ∈ C.response ∧ claimed (witnessPosition i) = 0)
    (a : ℕ)
    (hagreement : a ≤ (wordAgreement (oracle.directMask 0 .quadratic)
      (codeword (claimed - v1QuadraticCanonical candidate weights))).card) :
    finiteDot weights (fun row ↦ v1QuadraticResidual candidate row i) ∈
      responseLabelsAgreeingAtLeast C (oracle.directMask 0 .quadratic)
        (fun row ↦ -row (witnessPosition i)) a := by
  classical
  apply Finset.mem_image.mpr
  let offset := claimed - v1QuadraticCanonical candidate weights
  have hoffset : offset ∈ C.response := C.response.sub_mem haccept.1
    (v1QuadraticCanonical_mem candidate weights)
  refine ⟨offset, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hoffset, hagreement⟩, ?_⟩
  exact v1_quadratic_offset_label candidate weights i claimed haccept.2

/- An accepted V1 linear query is covered by the common residual and
agreement between the arbitrary committed linear mask and a response-code
offset. -/
omit [Fintype F] in
theorem v1_linear_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : SchemeVerifier.LinearAccepts C scheme statement
      weights claimed query (openSchemeOracle oracle query) 0)
    (remaining : Finset (Fin n))
    (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining) :
    query.coordinates ⊆ remaining ∪
      wordAgreement (oracle.directMask 0 .linear)
        (codeword (claimed - v1LinearCanonical candidate statement weights)) := by
  let actualCore : Word F n := fun j ↦
    ∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
      Verifier.coefficientRow C statement weights block row (codePosition j) *
        oracle.core block row j
  let decodedCore : Word F n :=
    codeword (v1LinearCanonical candidate statement weights)
  apply acceptedColumns_subset_residual_union_agreement query remaining
    actualCore decodedCore (codeword claimed) (oracle.directMask 0 .linear)
  · intro j hj
    have hlocal := haccept.2.2 ⟨j, hj⟩
    simpa [actualCore, scheme, openSchemeOracle,
      SchemeOracle.column, codeword] using hlocal
  · intro j hj hremaining
    have hnotBad : j ∉ candidate.badColumns := by
      intro hbadColumn
      exact hremaining (hbad (Finset.mem_inter.mpr ⟨hj, hbadColumn⟩))
    unfold actualCore decodedCore v1LinearCanonical
    simp only [codeword, Verifier.linearCore, Finset.sum_apply, rowMul_apply]
    apply Finset.sum_congr rfl
    intro block _
    apply Finset.sum_congr rfl
    intro row _
    have heq := candidate.row_eq_of_not_bad
      (Sum.inl ⟨block, row⟩) j hnotBad
    simpa [SchemeOracle.testedRow] using congrArg
      (fun value ↦ Verifier.coefficientRow C statement weights block row
        (codePosition j) * value) heq

omit [Fintype F] in
/-- The corresponding quadratic shared-column cover. -/
theorem v1_quadratic_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (weights : Fin nq → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : SchemeVerifier.QuadraticAccepts C scheme
      weights claimed query (openSchemeOracle oracle query) 0)
    (remaining : Finset (Fin n))
    (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining) :
    query.coordinates ⊆ remaining ∪
      wordAgreement (oracle.directMask 0 .quadratic)
        (codeword (claimed - v1QuadraticCanonical candidate weights)) := by
  let actualCore : Word F n := fun j ↦
    ∑ row : Fin nq, weights row *
      (oracle.core .left row j * oracle.core .right row j -
        oracle.core .output row j)
  let decodedCore : Word F n :=
    codeword (v1QuadraticCanonical candidate weights)
  apply acceptedColumns_subset_residual_union_agreement query remaining
    actualCore decodedCore (codeword claimed) (oracle.directMask 0 .quadratic)
  · intro j hj
    have hlocal := haccept.2.2 ⟨j, hj⟩
    simpa [actualCore, scheme, openSchemeOracle,
      SchemeOracle.column, codeword] using hlocal
  · intro j hj hremaining
    have hnotBad : j ∉ candidate.badColumns := by
      intro hbadColumn
      exact hremaining (hbad (Finset.mem_inter.mpr ⟨hj, hbadColumn⟩))
    unfold actualCore decodedCore v1QuadraticCanonical
    simp only [codeword, Verifier.quadraticCore, Finset.sum_apply,
      Pi.smul_apply, Pi.sub_apply, rowMul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro row _
    have hleft := candidate.row_eq_of_not_bad
      (Sum.inl ⟨CoreBlock.left, row⟩) j hnotBad
    have hright := candidate.row_eq_of_not_bad
      (Sum.inl ⟨CoreBlock.right, row⟩) j hnotBad
    have houtput := candidate.row_eq_of_not_bad
      (Sum.inl ⟨CoreBlock.output, row⟩) j hnotBad
    simp only [SchemeOracle.testedRow] at hleft hright houtput
    rw [hleft, hright, houtput]

end SchemeLiftCandidate

end Ligero.V1
