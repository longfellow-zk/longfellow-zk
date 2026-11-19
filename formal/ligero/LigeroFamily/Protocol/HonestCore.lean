import LigeroFamily.Protocol.IPCP

/-! # Mask-independent honest tableau -/

namespace LigeroFamily

open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype Equations]
variable {r w n nw nq : ℕ}

structure HonestCore
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (messages : CoreMessages F nw nq w) where
  row : (block : CoreBlock) → Fin (block.rowCount nw nq) → EvaluationRow F r w n
  row_mem : ∀ block index, row block index ∈ C.base
  row_witness : ∀ block index i,
    row block index (witnessPosition i) = messages block index i
  satisfies : statement.Satisfies messages

namespace HonestCore

variable {C : MultiplicativeCode F r w n}
variable {statement : ConstraintSystem F nw nq w Equations}
variable {messages : CoreMessages F nw nq w}

noncomputable def linearResponse
    (core : HonestCore C statement messages) (weights : Equations → F) :
    EvaluationRow F r w n :=
  Verifier.linearCore C statement weights core.row

noncomputable def quadraticResponse
    (core : HonestCore C statement messages) (weights : Fin nq → F) :
    EvaluationRow F r w n :=
  Verifier.quadraticCore weights core.row

theorem linearResponse_mem (core : HonestCore C statement messages)
    (weights : Equations → F) : core.linearResponse weights ∈ C.response := by
  unfold linearResponse Verifier.linearCore
  apply Submodule.sum_mem
  intro block _
  apply Submodule.sum_mem
  intro row _
  exact C.mul_mem (C.encode_mem 0 (statement.A weights block row))
    (core.row_mem block row)

/-- The special Ligero linear core vanishes on the complete random prefix
because every coefficient row has message values `encode 0 A_w`. -/
theorem linearResponse_random (core : HonestCore C statement messages)
    (weights : Equations → F) (i : Fin r) :
    core.linearResponse weights (randomPosition i) = 0 := by
  simp [linearResponse, Verifier.linearCore, Verifier.coefficientRow,
    rowMul, Finset.sum_apply]

omit [Fintype Equations] in
theorem quadraticResponse_mem (core : HonestCore C statement messages)
    (weights : Fin nq → F) : core.quadraticResponse weights ∈ C.response := by
  unfold quadraticResponse Verifier.quadraticCore
  apply Submodule.sum_mem
  intro row _
  apply C.response.smul_mem
  apply C.response.sub_mem
  · exact C.mul_mem (core.row_mem .left row) (core.row_mem .right row)
  · exact C.base_le_response (core.row_mem .output row)

theorem linearResponse_witness (core : HonestCore C statement messages)
    (weights : Equations → F) (i : Fin w) :
    core.linearResponse weights (witnessPosition i) =
      ∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
        statement.A weights block row i * messages block row i := by
  simp [linearResponse, Verifier.linearCore, rowMul,
    Verifier.coefficientRow, core.row_witness]

theorem linearResponse_sum (core : HonestCore C statement messages)
    (weights : Equations → F) :
    (∑ i : Fin w, core.linearResponse weights (witnessPosition i)) =
      statement.combinedTarget weights := by
  rw [show (∑ i : Fin w, core.linearResponse weights (witnessPosition i)) =
      ∑ i : Fin w, ∑ block : CoreBlock,
        ∑ row : Fin (block.rowCount nw nq),
          statement.A weights block row i * messages block row i by
        apply Finset.sum_congr rfl
        intro i _
        exact core.linearResponse_witness weights i]
  calc
    _ = ∑ equation : Equations, weights equation *
        statement.linearValue messages equation := by
      simp only [ConstraintSystem.A, ConstraintSystem.linearValue,
        Finset.mul_sum, Finset.sum_mul]
      let summand : (Fin w × CoreRow nw nq) → Equations → F :=
        fun index equation ↦ weights equation *
          statement.coefficient equation index.2.1 index.2.2 index.1 *
            messages index.2.1 index.2.2 index.1
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
                      messages blockRow.1 blockRow.2 i := by
              simp [summand, Fintype.sum_prod_type]
            _ = ∑ blockRow : CoreRow nw nq, ∑ i : Fin w,
                  weights equation *
                    statement.coefficient equation blockRow.1 blockRow.2 i *
                      messages blockRow.1 blockRow.2 i := Finset.sum_comm
            _ = _ := by simp [Fintype.sum_sigma, mul_assoc]
    _ = ∑ equation : Equations, weights equation * statement.target equation := by
      apply Finset.sum_congr rfl
      intro equation _
      rw [core.satisfies.1 equation]
    _ = _ := rfl

omit [Fintype Equations] in
theorem quadraticResponse_witness (core : HonestCore C statement messages)
    (weights : Fin nq → F) (i : Fin w) :
    core.quadraticResponse weights (witnessPosition i) = 0 := by
  simp only [quadraticResponse, Verifier.quadraticCore, Finset.sum_apply,
    Pi.smul_apply, Pi.sub_apply, rowMul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro row _
  rw [core.row_witness .left row i, core.row_witness .right row i,
    core.row_witness .output row i, core.satisfies.2 row i]
  ring

end HonestCore

end LigeroFamily
