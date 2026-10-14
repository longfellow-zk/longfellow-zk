import Ligero.V2.Protocol.Basic
import LigeroFamily.Soundness.Agreement
import LigeroFamily.Soundness.ProfiledLiftList

/-!
# Checked-mask arithmetic over common lift candidates

This is the V2-specific arithmetic layer. It works directly with
`SchemeLiftCandidate`; no legacy oracle, nearby encoding, or checked candidate
transport appears in the proof.
-/

namespace LigeroFamily

open Ligero.V2

open CodingTheory
open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq radius g : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : Ligero.V2.Oracle F nw nq n 1}

namespace SchemeLiftCandidate

abbrev checkedCore (candidate : SchemeLiftCandidate C oracle radius)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
  candidate.decodedCore block row

def checkedMask (candidate : SchemeLiftCandidate C oracle radius)
    (kind : Ligero.V2.Mask) : EvaluationRow F r w n :=
  candidate.row (Sum.inr (0, kind))

abbrev checkedMessages (candidate : SchemeLiftCandidate C oracle radius) :=
  candidate.decodedMessages

abbrev checkedLinearResidual (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations) :=
  candidate.linearResidual statement

abbrev checkedQuadraticResidual (candidate : SchemeLiftCandidate C oracle radius) :=
  candidate.quadraticResidual

noncomputable def checkedLinearCanonical
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) : EvaluationRow F r w n :=
  Ligero.V2.Verifier.linearResponse C M statement weights candidate.checkedCore
    candidate.checkedMask

noncomputable def checkedQuadraticCanonical
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (weights : Fin nq → F) : EvaluationRow F r w n :=
  Ligero.V2.Verifier.quadraticResponse C M weights candidate.checkedCore
    candidate.checkedMask

omit [Fintype F] [DecidableEq Equations] in
theorem checkedLinearCanonical_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) :
    candidate.checkedLinearCanonical M statement weights ∈ C.response := by
  simp only [checkedLinearCanonical, Ligero.V2.Verifier.linearResponse,
    Verifier.linearCore, Ligero.V2.Verifier.linearMask]
  apply C.response.add_mem
  · apply Submodule.sum_mem
    intro block _
    apply Submodule.sum_mem
    intro row _
    exact C.mul_mem (C.encode_mem 0 (statement.A weights block row))
      (candidate.row_mem (Sum.inl ⟨block, row⟩))
  · apply C.response.add_mem
    · exact M.vanishing_mul_mem
        (candidate.row_mem (Sum.inr (0, .linearVCoefficient)))
    · exact C.mul_mem C.zR_mem
        (candidate.row_mem (Sum.inr (0, .linearZRCoefficient)))

omit [Fintype F] [DecidableEq Equations] in
/-- Every decoded canonical linear response has the same zero random prefix
as the honest response, independently of whether the decoded messages satisfy
the statement. -/
theorem checkedLinearCanonical_random
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (i : Fin r) :
    candidate.checkedLinearCanonical M statement weights (randomPosition i) =
      0 := by
  change Verifier.linearCore C statement weights candidate.checkedCore
        (randomPosition i) +
      (M.vanishing (randomPosition i) *
          candidate.checkedMask .linearVCoefficient (randomPosition i) +
        C.zR (randomPosition i) *
          candidate.checkedMask .linearZRCoefficient (randomPosition i)) = 0
  have hcore : Verifier.linearCore C statement weights candidate.checkedCore
      (randomPosition i) = 0 := by
    simp [Verifier.linearCore, Verifier.coefficientRow, rowMul,
      Finset.sum_apply]
  rw [hcore, show M.vanishing (randomPosition i) = 0 from
    M.vanishing_message (Sum.inl i), C.zR_random]
  ring

omit [Fintype F] in
theorem checkedQuadraticCanonical_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (weights : Fin nq → F) :
    candidate.checkedQuadraticCanonical M weights ∈ C.response := by
  simp only [checkedQuadraticCanonical, Ligero.V2.Verifier.quadraticResponse,
    Verifier.quadraticCore, Ligero.V2.Verifier.quadraticMask]
  apply C.response.add_mem
  · apply Submodule.sum_mem
    intro row _
    apply C.response.smul_mem
    apply C.response.sub_mem
    · exact C.mul_mem
        (candidate.row_mem (Sum.inl ⟨CoreBlock.left, row⟩))
        (candidate.row_mem (Sum.inl ⟨CoreBlock.right, row⟩))
    · exact C.base_le_response
        (candidate.row_mem (Sum.inl ⟨CoreBlock.output, row⟩))
  · apply C.response.add_mem
    · exact M.vanishing_mul_mem
        (candidate.row_mem (Sum.inr (0, .quadraticVCoefficient)))
    · exact C.mul_mem C.zW_mem
        (candidate.row_mem (Sum.inr (0, .quadraticZWCoefficient)))

def checkedLinearZRCoefficientSum
    (candidate : SchemeLiftCandidate C oracle radius) : F :=
  ∑ i : Fin w,
    candidate.checkedMask .linearZRCoefficient (witnessPosition i)

omit [Fintype F] [DecidableEq Equations] in
theorem checkedLinearCanonical_witness_sum
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) :
    (∑ i : Fin w,
      candidate.checkedLinearCanonical M statement weights
        (witnessPosition i)) =
      finiteDot weights (candidate.checkedLinearResidual statement) +
        statement.combinedTarget weights +
          candidate.checkedLinearZRCoefficientSum := by
  simp only [checkedLinearCanonical, Ligero.V2.Verifier.linearResponse,
    Verifier.linearCore, Ligero.V2.Verifier.linearMask, Pi.add_apply,
    Finset.sum_add_distrib, rowMul_apply, Finset.sum_apply]
  have hcore :
      (∑ i : Fin w, ∑ block : CoreBlock,
        ∑ row : Fin (block.rowCount nw nq),
          Verifier.coefficientRow C statement weights block row
              (witnessPosition i) *
            candidate.checkedCore block row (witnessPosition i)) =
      ∑ equation : Equations, weights equation *
        statement.linearValue candidate.checkedMessages equation := by
    simp only [Verifier.coefficientRow, MultiplicativeCode.encode_witness,
      ConstraintSystem.A, ConstraintSystem.linearValue, Finset.mul_sum,
      Finset.sum_mul]
    let summand : (Fin w × CoreRow nw nq) → Equations → F :=
      fun index equation ↦ weights equation *
        statement.coefficient equation index.2.1 index.2.2 index.1 *
          candidate.checkedMessages index.2.1 index.2.2 index.1
    calc
      _ = ∑ index : Fin w × CoreRow nw nq,
          ∑ equation : Equations, summand index equation := by
        simp [summand, Fintype.sum_prod_type, Fintype.sum_sigma,
          checkedMessages, checkedCore, decodedMessages, decodedCore,
          witnessValues, mul_assoc]
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
                    candidate.checkedMessages blockRow.1 blockRow.2 i := by
            simp [summand, Fintype.sum_prod_type]
          _ = ∑ blockRow : CoreRow nw nq, ∑ i : Fin w,
                weights equation *
                  statement.coefficient equation blockRow.1 blockRow.2 i *
                    candidate.checkedMessages blockRow.1 blockRow.2 i :=
            Finset.sum_comm
          _ = _ := by simp [Fintype.sum_sigma, mul_assoc]
  rw [hcore]
  simp_rw [show ∀ i : Fin w, M.vanishing (witnessPosition i) = 0 from
    fun i ↦ M.vanishing_message (Sum.inr i), C.zR_witness]
  simp only [zero_mul, Finset.sum_const_zero, zero_add]
  unfold finiteDot checkedLinearResidual linearResidual checkedMessages decodedMessages
    ConstraintSystem.combinedTarget checkedLinearZRCoefficientSum
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring_nf

omit [Fintype F] in
theorem checkedQuadraticCanonical_witness
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (weights : Fin nq → F) (i : Fin w) :
    candidate.checkedQuadraticCanonical M weights (witnessPosition i) =
      finiteDot weights (fun row ↦ candidate.checkedQuadraticResidual row i) := by
  simp only [checkedQuadraticCanonical, Ligero.V2.Verifier.quadraticResponse,
    Verifier.quadraticCore, Ligero.V2.Verifier.quadraticMask, finiteDot,
    checkedQuadraticResidual, quadraticResidual, checkedCore,
    decodedMessages, decodedCore, witnessValues,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply,
    rowMul_apply, smul_eq_mul]
  rw [show M.vanishing (witnessPosition i) = 0 from
      M.vanishing_message (Sum.inr i), C.zW_witness]
  simp

omit [Fintype F] [DecidableEq Equations] in
theorem checked_linear_local_canonical_at
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : SchemeVerifier.LinearAccepts C (scheme C M)
      statement weights claimed query (openSchemeOracle oracle query) 0)
    (j : Fin n) (hj : j ∈ query.coordinates)
    (hgood : j ∉ candidate.badColumns) :
    claimed (codePosition j) =
      candidate.checkedLinearCanonical M statement weights (codePosition j) := by
  let qj : ↑query.coordinates := ⟨j, hj⟩
  have hlocal := haccept.2.2 qj
  have hcore (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
    candidate.row_eq_of_not_bad (Sum.inl ⟨block, row⟩) j hgood
  have hmask (kind : Mask) :=
    candidate.row_eq_of_not_bad (Sum.inr (0, kind)) j hgood
  simp only [SchemeOracle.testedRow] at hcore hmask
  simp [qj, checkedLinearCanonical, checkedCore, decodedCore, checkedMask,
    Ligero.V2.Verifier.linearResponse, Verifier.linearCore,
    Ligero.V2.Verifier.linearMask,
    scheme, openSchemeOracle, SchemeOracle.column, hcore, hmask]
    at hlocal ⊢
  rw [hlocal]

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] in
theorem checked_quadratic_local_canonical_at
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (weights : Fin nq → F)
    (claimed : EvaluationRow F r w n) (query : QuerySet n r)
    (haccept : SchemeVerifier.QuadraticAccepts C (scheme C M)
      weights claimed query (openSchemeOracle oracle query) 0)
    (j : Fin n) (hj : j ∈ query.coordinates)
    (hgood : j ∉ candidate.badColumns) :
    claimed (codePosition j) =
      candidate.checkedQuadraticCanonical M weights (codePosition j) := by
  let qj : ↑query.coordinates := ⟨j, hj⟩
  have hlocal := haccept.2.2 qj
  have hcore (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
    candidate.row_eq_of_not_bad (Sum.inl ⟨block, row⟩) j hgood
  have hmask (kind : Mask) :=
    candidate.row_eq_of_not_bad (Sum.inr (0, kind)) j hgood
  simp only [SchemeOracle.testedRow] at hcore hmask
  simp [qj, checkedQuadraticCanonical, checkedCore, decodedCore, checkedMask,
    Ligero.V2.Verifier.quadraticResponse, Verifier.quadraticCore,
    Ligero.V2.Verifier.quadraticMask, Ligero.V2.scheme, openSchemeOracle,
    SchemeOracle.column, hcore, hmask] at hlocal ⊢
  rw [hlocal]

omit [Fintype F] [DecidableEq Equations] in
theorem checked_linear_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (statement : ConstraintSystem F nw nq w Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : SchemeVerifier.LinearAccepts C (scheme C M)
      statement weights claimed query (openSchemeOracle oracle query) 0)
    (remaining : Finset (Fin n)) (hremaining : remaining.card ≤ g)
    (hk : 0 < C.k) (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining)
    (hnonexceptional :
      finiteDot weights (candidate.checkedLinearResidual statement) ≠
        -candidate.checkedLinearZRCoefficientSum) :
    query.coordinates ⊆ remaining ∪ responseAgreement claimed
        (candidate.checkedLinearCanonical M statement weights) ∧
      (remaining ∪ responseAgreement claimed
        (candidate.checkedLinearCanonical M statement weights)).card ≤
          2 * C.k + g - 1 := by
  have hne : claimed ≠ candidate.checkedLinearCanonical M statement weights := by
    intro heq
    apply hnonexceptional
    have hsum := candidate.checkedLinearCanonical_witness_sum M statement weights
    rw [← heq, haccept.2.1] at hsum
    linear_combination -hsum
  have hagreement := responseAgreement_card_le C haccept.1
    (candidate.checkedLinearCanonical_mem M statement weights) hne
  have htwo : 1 ≤ 2 * C.k := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Nat.ne_of_gt hk))
  constructor
  · intro j hj
    by_cases hjremaining : j ∈ remaining
    · exact Finset.mem_union_left _ hjremaining
    · apply Finset.mem_union_right
      apply (mem_responseAgreement _ _ _).mpr
      apply candidate.checked_linear_local_canonical_at M statement weights
        claimed query haccept j hj
      intro hjbad
      exact hjremaining (hbad (Finset.mem_inter.mpr ⟨hj, hjbad⟩))
  · calc
      _ ≤ remaining.card +
          (responseAgreement claimed
            (candidate.checkedLinearCanonical M statement weights)).card :=
        Finset.card_union_le _ _
      _ ≤ g + (2 * C.k - 1) := Nat.add_le_add hremaining hagreement
      _ ≤ 2 * C.k + g - 1 := by omega

omit [Fintype F] in
theorem checked_quadratic_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (M : C.MaskingBasis) (weights : Fin nq → F) (i : Fin w)
    (claimed : EvaluationRow F r w n) (query : QuerySet n r)
    (haccept : SchemeVerifier.QuadraticAccepts C (scheme C M)
      weights claimed query (openSchemeOracle oracle query) 0)
    (remaining : Finset (Fin n)) (hremaining : remaining.card ≤ g)
    (hk : 0 < C.k) (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining)
    (hnonexceptional :
      finiteDot weights (fun row ↦ candidate.checkedQuadraticResidual row i) ≠ 0) :
    query.coordinates ⊆ remaining ∪ responseAgreement claimed
        (candidate.checkedQuadraticCanonical M weights) ∧
      (remaining ∪ responseAgreement claimed
        (candidate.checkedQuadraticCanonical M weights)).card ≤
          2 * C.k + g - 1 := by
  have hne : claimed ≠ candidate.checkedQuadraticCanonical M weights := by
    intro heq
    apply hnonexceptional
    rw [← candidate.checkedQuadraticCanonical_witness M weights i,
      ← heq, haccept.2.1 i]
  have hagreement := responseAgreement_card_le C haccept.1
    (candidate.checkedQuadraticCanonical_mem M weights) hne
  have htwo : 1 ≤ 2 * C.k := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Nat.ne_of_gt hk))
  constructor
  · intro j hj
    by_cases hjremaining : j ∈ remaining
    · exact Finset.mem_union_left _ hjremaining
    · apply Finset.mem_union_right
      apply (mem_responseAgreement _ _ _).mpr
      apply candidate.checked_quadratic_local_canonical_at M weights claimed
        query haccept j hj
      intro hjbad
      exact hjremaining (hbad (Finset.mem_inter.mpr ⟨hj, hjbad⟩))
  · calc
      _ ≤ remaining.card +
          (responseAgreement claimed
            (candidate.checkedQuadraticCanonical M weights)).card :=
        Finset.card_union_le _ _
      _ ≤ g + (2 * C.k - 1) := Nat.add_le_add hremaining hagreement
      _ ≤ 2 * C.k + g - 1 := by omega

end SchemeLiftCandidate

end LigeroFamily
