import LigeroFamily.Soundness.DirectProductExtractor
import LigeroFamily.Soundness.PolicyProfiledMaster
import LigeroFamily.Soundness.Agreement

/-! # Direct-product arithmetic over common lift candidates -/

namespace LigeroFamily

open CodingTheory MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {logicalWidth r w n nw nq radius g : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {M : C.MaskingBasis}
variable {layout : ConstraintLayout F logicalWidth w}
variable {oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1}

namespace SchemeLiftCandidate

abbrev directCore (candidate : SchemeLiftCandidate C oracle radius)
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
  candidate.decodedCore block row

def directMask (candidate : SchemeLiftCandidate C oracle radius)
    (kind : LinearConstraintMask) : EvaluationRow F r w n :=
  candidate.row (Sum.inr (0, kind))

def directMessages (candidate : SchemeLiftCandidate C oracle radius) :
    CoreMessages F nw nq logicalWidth :=
  layoutCoreMessages layout candidate.directCore

def directLinearResidual
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (equation : Equations) : F :=
  statement.linearValue (candidate.directMessages (layout := layout)) equation -
    statement.target equation

def directQuadraticResidual
    (candidate : SchemeLiftCandidate C oracle radius)
    (row : Fin nq) (i : Fin logicalWidth) : F :=
  candidate.directMessages (layout := layout) .left row i *
    candidate.directMessages (layout := layout) .right row i -
    candidate.directMessages (layout := layout) .output row i

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] in
theorem direct_residual_of_not_satisfies
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (hns : ¬statement.Satisfies (candidate.directMessages (layout := layout))) :
    candidate.directLinearResidual (layout := layout) statement ≠ 0 ∨
      ∃ i, (fun row => candidate.directQuadraticResidual
        (layout := layout) row i) ≠ 0 := by
  exact statement.residual_of_not_satisfies
    (candidate.directMessages (layout := layout)) hns

noncomputable def directLinearCanonical
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) : EvaluationRow F r w n :=
  DirectVerifier.linearResponse C M layout statement weights
    candidate.directCore candidate.directMask

omit [Fintype F] [DecidableEq Equations] in
theorem directLinearCanonical_mem
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) :
    candidate.directLinearCanonical (M := M) (layout := layout)
      statement weights ∈ C.response := by
  unfold directLinearCanonical DirectVerifier.linearResponse
  apply C.response.add_mem
  · unfold DirectVerifier.linearCore
    apply Submodule.sum_mem
    intro block _
    apply Submodule.sum_mem
    intro row _
    exact C.mul_mem
      (C.encode_mem 0 (layout.extend (statement.A weights block row)))
      (candidate.row_mem (Sum.inl ⟨block, row⟩))
  · unfold DirectVerifier.linearMask
    apply C.response.add_mem
    · exact M.vanishing_mul_mem
        (candidate.row_mem (Sum.inr (0, .vCoefficient)))
    · exact C.mul_mem C.zR_mem
        (candidate.row_mem (Sum.inr (0, .zRCoefficient)))

def directLinearZRCoefficientSum
    (candidate : SchemeLiftCandidate C oracle radius) : F :=
  ∑ i : Fin logicalWidth,
    candidate.directMask .zRCoefficient
      (logicalWitnessPosition layout i)

omit [Fintype F] [DecidableEq Equations] in
theorem directLinearCanonical_logical
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) (i : Fin logicalWidth) :
    candidate.directLinearCanonical (M := M) (layout := layout) statement weights
        (logicalWitnessPosition layout i) =
      (∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
        statement.A weights block row i *
          candidate.directMessages (layout := layout) block row i) +
        candidate.directMask .zRCoefficient
          (logicalWitnessPosition layout i) := by
  simp only [directLinearCanonical, DirectVerifier.linearResponse,
    DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
    Finset.sum_apply, rowMul_apply, DirectVerifier.coefficientRow]
  rw [show M.vanishing (logicalWitnessPosition layout i) = 0 from
      M.vanishing_message (Sum.inr (layout.logical i)),
    show C.zR (logicalWitnessPosition layout i) = 1 from
      C.zR_witness (layout.logical i)]
  simp only [zero_mul, one_mul, zero_add]
  simp [logicalWitnessPosition, directMessages, layoutCoreMessages,
    logicalValues, layout.extend_logical]

omit [Fintype F] [DecidableEq Equations] in
theorem directLinearCanonical_logical_sum
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) :
    (∑ i : Fin logicalWidth,
      candidate.directLinearCanonical (M := M) (layout := layout) statement weights
        (logicalWitnessPosition layout i)) =
      finiteDot weights (candidate.directLinearResidual (layout := layout) statement) +
        statement.combinedTarget weights +
          candidate.directLinearZRCoefficientSum (layout := layout) := by
  calc
    _ = ∑ i : Fin logicalWidth,
        ((∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
          statement.A weights block row i *
            candidate.directMessages (layout := layout) block row i) +
          candidate.directMask .zRCoefficient
            (logicalWitnessPosition layout i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact candidate.directLinearCanonical_logical (M := M)
        (layout := layout) statement weights i
    _ = (∑ i : Fin logicalWidth, ∑ block : CoreBlock,
          ∑ row : Fin (block.rowCount nw nq),
            statement.A weights block row i *
              candidate.directMessages (layout := layout) block row i) +
        candidate.directLinearZRCoefficientSum (layout := layout) := by
      exact Finset.sum_add_distrib
    _ = _ := by
      congr 1
      unfold finiteDot directLinearResidual ConstraintSystem.combinedTarget
      simp only [mul_sub, Finset.sum_sub_distrib]
      have hcore :
          (∑ i : Fin logicalWidth, ∑ block : CoreBlock,
            ∑ row : Fin (block.rowCount nw nq),
              statement.A weights block row i *
                candidate.directMessages (layout := layout) block row i) =
          ∑ equation : Equations, weights equation *
            statement.linearValue
              (candidate.directMessages (layout := layout)) equation := by
        simp only [ConstraintSystem.A, ConstraintSystem.linearValue,
          Finset.mul_sum, Finset.sum_mul]
        let summand : (Fin logicalWidth × CoreRow nw nq) → Equations → F :=
          fun index equation => weights equation *
            statement.coefficient equation index.2.1 index.2.2 index.1 *
              candidate.directMessages (layout := layout)
                index.2.1 index.2.2 index.1
        calc
          _ = ∑ index : Fin logicalWidth × CoreRow nw nq,
              ∑ equation : Equations, summand index equation := by
            simp [summand, Fintype.sum_prod_type, Fintype.sum_sigma, mul_assoc]
          _ = ∑ equation : Equations,
              ∑ index : Fin logicalWidth × CoreRow nw nq,
                summand index equation := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro equation _
            calc
              (∑ index : Fin logicalWidth × CoreRow nw nq,
                  summand index equation) =
                  ∑ i : Fin logicalWidth, ∑ blockRow : CoreRow nw nq,
                    weights equation *
                      statement.coefficient equation blockRow.1 blockRow.2 i *
                        candidate.directMessages (layout := layout)
                          blockRow.1 blockRow.2 i := by
                simp [summand, Fintype.sum_prod_type]
              _ = ∑ blockRow : CoreRow nw nq, ∑ i : Fin logicalWidth,
                    weights equation *
                      statement.coefficient equation blockRow.1 blockRow.2 i *
                        candidate.directMessages (layout := layout)
                          blockRow.1 blockRow.2 i := Finset.sum_comm
              _ = _ := by simp [Fintype.sum_sigma, mul_assoc]
      rw [hcore]
      ring

omit [Fintype F] [DecidableEq Equations] in
theorem direct_linear_local_canonical_at
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : DirectVerifier.LinearAccepts C M layout statement weights claimed
      query (openSchemeOracle oracle query) 0)
    (j : Fin n) (hj : j ∈ query.coordinates)
    (hgood : j ∉ candidate.badColumns) :
    claimed (codePosition j) =
      candidate.directLinearCanonical (M := M) (layout := layout)
        statement weights (codePosition j) := by
  let qj : ↑query.coordinates := ⟨j, hj⟩
  have hlocal := haccept.2.2 qj
  have hcore (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :=
    candidate.row_eq_of_not_bad (Sum.inl ⟨block, row⟩) j hgood
  have hmask (kind : LinearConstraintMask) :=
    candidate.row_eq_of_not_bad (Sum.inr (0, kind)) j hgood
  simp only [SchemeOracle.testedRow] at hcore hmask
  simp [qj, directLinearCanonical, directCore, decodedCore, directMask,
    DirectVerifier.linearResponse, DirectVerifier.linearCore,
    DirectVerifier.linearMask, openSchemeOracle, SchemeOracle.column,
    hcore, hmask] at hlocal ⊢
  rw [hlocal]
  ring

omit [Fintype F] [DecidableEq Equations] in
theorem direct_linear_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (weights : Equations → F) (claimed : EvaluationRow F r w n)
    (query : QuerySet n r)
    (haccept : DirectVerifier.LinearAccepts C M layout statement weights claimed
      query (openSchemeOracle oracle query) 0)
    (remaining : Finset (Fin n)) (hremaining : remaining.card ≤ g)
    (hk : 0 < C.k) (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining)
    (hnonexceptional :
      finiteDot weights (candidate.directLinearResidual (layout := layout) statement) ≠
        -candidate.directLinearZRCoefficientSum (layout := layout)) :
    query.coordinates ⊆ remaining ∪ responseAgreement claimed
        (candidate.directLinearCanonical (M := M) (layout := layout)
          statement weights) ∧
      (remaining ∪ responseAgreement claimed
        (candidate.directLinearCanonical (M := M) (layout := layout)
          statement weights)).card ≤
          2 * C.k + g - 1 := by
  have hne : claimed ≠ candidate.directLinearCanonical (M := M)
      (layout := layout) statement weights := by
    intro heq
    apply hnonexceptional
    have hsum := candidate.directLinearCanonical_logical_sum (M := M)
      (layout := layout) statement weights
    rw [← heq, haccept.2.1] at hsum
    linear_combination -hsum
  have hagreement := responseAgreement_card_le C haccept.1
    (candidate.directLinearCanonical_mem (M := M) (layout := layout)
      statement weights) hne
  have htwo : 1 ≤ 2 * C.k := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Nat.ne_of_gt hk))
  constructor
  · intro j hj
    by_cases hjremaining : j ∈ remaining
    · exact Finset.mem_union_left _ hjremaining
    · apply Finset.mem_union_right
      apply (mem_responseAgreement _ _ _).mpr
      apply candidate.direct_linear_local_canonical_at statement weights
        claimed query haccept j hj
      intro hjbad
      exact hjremaining (hbad (Finset.mem_inter.mpr ⟨hj, hjbad⟩))
  · calc
      _ ≤ remaining.card +
          (responseAgreement claimed
            (candidate.directLinearCanonical (M := M) (layout := layout)
              statement weights)).card :=
        Finset.card_union_le _ _
      _ ≤ g + (2 * C.k - 1) := Nat.add_le_add hremaining hagreement
      _ ≤ 2 * C.k + g - 1 := by omega

noncomputable def directQuadraticWord
    (candidate : SchemeLiftCandidate C oracle radius) (row : Fin nq) :
    EvaluationRow F r w n :=
  rowMul (candidate.directCore .left row) (candidate.directCore .right row) -
    candidate.directCore .output row

omit [Fintype F] in
theorem directQuadraticWord_mem
    (candidate : SchemeLiftCandidate C oracle radius) (row : Fin nq) :
    candidate.directQuadraticWord row ∈ C.response :=
  C.response.sub_mem
    (C.mul_mem
      (candidate.row_mem (Sum.inl ⟨.left, row⟩))
      (candidate.row_mem (Sum.inl ⟨.right, row⟩)))
    (C.base_le_response (candidate.row_mem (Sum.inl ⟨.output, row⟩)))

omit [Fintype F] in
theorem direct_quadratic_query_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (row : Fin nq) (i : Fin logicalWidth)
    (hresidual : candidate.directQuadraticResidual (layout := layout) row i ≠ 0)
    (query : QuerySet n r)
    (haccept : DirectVerifier.DirectProductAccepts query
      (openSchemeOracle oracle query))
    (remaining : Finset (Fin n)) (hremaining : remaining.card ≤ g)
    (hk : 0 < C.k) (hbad : query.coordinates ∩ candidate.badColumns ⊆ remaining) :
    query.coordinates ⊆ remaining ∪
        responseAgreement (candidate.directQuadraticWord row) 0 ∧
      (remaining ∪ responseAgreement
        (candidate.directQuadraticWord row) 0).card ≤ 2 * C.k + g - 1 := by
  have hne : candidate.directQuadraticWord row ≠ 0 := by
    intro hzero
    apply hresidual
    have hvalue := congrFun hzero (logicalWitnessPosition layout i)
    simpa [directQuadraticWord, directQuadraticResidual, directMessages,
      layoutCoreMessages, logicalValues, directCore, rowMul] using hvalue
  have hagreement := responseAgreement_card_le C
    (candidate.directQuadraticWord_mem row) C.response.zero_mem hne
  have htwo : 1 ≤ 2 * C.k := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (Nat.ne_of_gt hk))
  constructor
  · intro j hj
    by_cases hjremaining : j ∈ remaining
    · exact Finset.mem_union_left _ hjremaining
    · apply Finset.mem_union_right
      apply (mem_responseAgreement _ _ _).mpr
      have hgood : j ∉ candidate.badColumns := by
        intro hjbad
        exact hjremaining (hbad (Finset.mem_inter.mpr ⟨hj, hjbad⟩))
      let qj : ↑query.coordinates := ⟨j, hj⟩
      have hproduct := haccept qj row
      have hleft := candidate.row_eq_of_not_bad (Sum.inl ⟨.left, row⟩) j hgood
      have hright := candidate.row_eq_of_not_bad (Sum.inl ⟨.right, row⟩) j hgood
      have houtput := candidate.row_eq_of_not_bad (Sum.inl ⟨.output, row⟩) j hgood
      simp only [SchemeOracle.testedRow] at hleft hright houtput
      change oracle.core .left row j * oracle.core .right row j =
        oracle.core .output row j at hproduct
      rw [hleft, hright, houtput] at hproduct
      simpa [directQuadraticWord, directCore, decodedCore] using
        sub_eq_zero.mpr hproduct
  · calc
      _ ≤ remaining.card +
          (responseAgreement (candidate.directQuadraticWord row) 0).card :=
        Finset.card_union_le _ _
      _ ≤ g + (2 * C.k - 1) := Nat.add_le_add hremaining hagreement
      _ ≤ 2 * C.k + g - 1 := by omega

end SchemeLiftCandidate

/-- The direct-product analogue of `NoDecodedSolution`: no member of the
oracle's lift list, read through `layout`, satisfies the statement.  V3 decodes
its candidates with `directMessages` rather than `decodedMessages`, so it needs
its own name for the same idea. -/
def NoDirectSolution (C : MultiplicativeCode F r w n)
    (layout : ConstraintLayout F logicalWidth w)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1) (radius : ℕ)
    (statement : ConstraintSystem F nw nq logicalWidth Equations) : Prop :=
  ∀ candidate : SchemeLiftCandidate C oracle radius,
    ¬statement.Satisfies (candidate.directMessages (layout := layout))

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] in
theorem NoDirectSolution.of_not_language
    {statement : ConstraintSystem F nw nq logicalWidth Equations}
    (hfalse : ¬statement.Language) :
    NoDirectSolution C layout oracle radius statement :=
  fun _ hsat => hfalse ⟨_, hsat⟩

end LigeroFamily
