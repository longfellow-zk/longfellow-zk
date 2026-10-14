import polygero.Protocol.Legacy.Verifier

/-! Decoded candidate witnesses and the global linear-functional identities. -/

namespace LigeroFamily.PolynomialDirect
open Finset Polynomial
open MultiplicativeCode
open RecursivePolygero.Local
variable {F Equations : Type*} [Field F] [DecidableEq F]
variable [Fintype Equations]
variable {q r w n nw nq s : Nat}

/-- Messages decoded from the base-row polynomials at Ligero's logical
witness positions. -/
noncomputable def decodedMessages
    (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w)) :
    CoreMessages F nw nq q := fun block row i =>
  (rows (coreIndex block row) : F[X]).eval
    (D.point (logicalWitnessPosition layout i))

omit [DecidableEq F] in
theorem decodedMessages_quadratic
    (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (hproduct : ∀ row : Fin nq,
      (rows (leftIndex row) : F[X]) * (rows (rightIndex row) : F[X]) =
        (rows (outputIndex row) : F[X])) :
    ∀ (row : Fin nq) i,
      decodedMessages D layout rows .left row i *
          decodedMessages D layout rows .right row i =
        decodedMessages D layout rows .output row i := by
  intro row i
  have heval := congrArg
    (fun p : F[X] => p.eval (D.point (logicalWitnessPosition layout i)))
    (hproduct row)
  simpa [decodedMessages, leftIndex, rightIndex, outputIndex,
    Polynomial.eval_mul] using heval

omit [DecidableEq F] [Fintype Equations] in
/-- A false statement has no satisfying candidate witness. The decoded tuple
satisfies the multiplication constraints, so it fails a linear constraint and
has a nonzero linear residual. -/
theorem linearResidual_ne_zero_of_not_language
    (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (hproduct : ∀ row : Fin nq,
      (rows (leftIndex row) : F[X]) * (rows (rightIndex row) : F[X]) =
        (rows (outputIndex row) : F[X]))
    (hfalse : ¬statement.Language) :
    (fun equation => statement.linearValue (decodedMessages D layout rows) equation -
      statement.target equation) ≠ 0 := by
  have hnoWitness : ∀ messages, ¬statement.Satisfies messages :=
    not_exists.mp hfalse
  have hnot : ¬statement.Satisfies (decodedMessages D layout rows) :=
    hnoWitness (decodedMessages D layout rows)
  have hquadratic := decodedMessages_quadratic D layout rows hproduct
  have hlinear : ¬∀ equation,
      statement.linearValue (decodedMessages D layout rows) equation =
        statement.target equation := by
    simpa only [ConstraintSystem.Satisfies, hquadratic, implies_true, and_true] using hnot
  obtain ⟨equation, hfailed⟩ := not_forall.mp hlinear
  exact Function.ne_iff.mpr ⟨equation, sub_ne_zero.mpr hfailed⟩

/-- Linear residual of the messages decoded from a polynomial row tuple. -/
noncomputable def decodedLinearResidual
    (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (equation : Equations) : F :=
  statement.linearValue (decodedMessages D layout rows) equation -
    statement.target equation

/-- Logical-position sum of the `zR`-coefficient mask decoded from a
polynomial row tuple. -/
noncomputable def decodedZRMaskSum
    (D : ReedSolomon.Domain F r w n)
    (layout : ConstraintLayout F q w)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w)) : F :=
  ∑ i : Fin q, (rows (maskIndex (.zRCoefficient : LinearConstraintMask)) : F[X]).eval
    (D.point (logicalWitnessPosition layout i))

omit [DecidableEq F] in
theorem responseCanonical_logical
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (i : Fin q) :
    ((responseSemantics D hk hprimary layout statement weights).canonical
        B rows : F[X]).eval (D.point (logicalWitnessPosition layout i)) =
      (∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
        statement.A weights block row i *
          decodedMessages D layout rows block row i) +
        (rows (maskIndex (.zRCoefficient : LinearConstraintMask)) : F[X]).eval
          (D.point (logicalWitnessPosition layout i)) := by
  change ((responsePolynomial D hk
      (linearRow D hk layout statement weights rows)
      (linearRow_mem D hk layout statement weights rows) :
        DegreeLT F (2 * (r + w))) : F[X]).eval
      (D.point (logicalWitnessPosition layout i)) = _
  rw [responsePolynomial_eval D hk _ _ (logicalWitnessPosition layout i)]
  simp only [linearRow, DirectVerifier.linearResponse,
    DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
    Finset.sum_apply, rowMul_apply, DirectVerifier.coefficientRow]
  rw [show (ReedSolomon.maskingBasis D hk).vanishing
        (logicalWitnessPosition layout i) = 0 from
      (ReedSolomon.maskingBasis D hk).vanishing_message
        (Sum.inr (layout.logical i)),
    show (ReedSolomon.multiplicativeCode D hk).zR
        (logicalWitnessPosition layout i) = 1 from
      (ReedSolomon.multiplicativeCode D hk).zR_witness (layout.logical i)]
  simp only [zero_mul, one_mul, zero_add, decodedCore, decodedMask, evaluationRow]
  simp [logicalWitnessPosition, decodedMessages, layout.extend_logical]

omit [DecidableEq F] in
theorem responseCanonical_logical_sum
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w)) :
    (∑ i : Fin q,
      ((responseSemantics D hk hprimary layout statement weights).canonical
        B rows : F[X]).eval (D.point (logicalWitnessPosition layout i))) =
      finiteDot weights (decodedLinearResidual D layout statement rows) +
        statement.combinedTarget weights + decodedZRMaskSum D layout rows := by
  calc
    _ = ∑ i : Fin q,
        ((∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
          statement.A weights block row i *
            decodedMessages D layout rows block row i) +
          (rows (maskIndex (.zRCoefficient : LinearConstraintMask)) : F[X]).eval
            (D.point (logicalWitnessPosition layout i))) := by
      apply Finset.sum_congr rfl
      intro i _
      exact responseCanonical_logical D hk hprimary layout statement weights B rows i
    _ = (∑ i : Fin q, ∑ block : CoreBlock,
          ∑ row : Fin (block.rowCount nw nq),
            statement.A weights block row i *
              decodedMessages D layout rows block row i) +
        decodedZRMaskSum D layout rows := by
      exact Finset.sum_add_distrib
    _ = _ := by
      congr 1
      unfold finiteDot decodedLinearResidual ConstraintSystem.combinedTarget
      simp only [mul_sub, Finset.sum_sub_distrib]
      have hcore :
          (∑ i : Fin q, ∑ block : CoreBlock,
            ∑ row : Fin (block.rowCount nw nq),
              statement.A weights block row i *
                decodedMessages D layout rows block row i) =
          ∑ equation : Equations, weights equation *
            statement.linearValue (decodedMessages D layout rows) equation := by
        simp only [ConstraintSystem.A, ConstraintSystem.linearValue,
          Finset.mul_sum, Finset.sum_mul]
        let summand : (Fin q × CoreRow nw nq) → Equations → F :=
          fun index equation => weights equation *
            statement.coefficient equation index.2.1 index.2.2 index.1 *
              decodedMessages D layout rows index.2.1 index.2.2 index.1
        calc
          _ = ∑ index : Fin q × CoreRow nw nq,
              ∑ equation : Equations, summand index equation := by
            simp [summand, Fintype.sum_prod_type, Fintype.sum_sigma, mul_assoc]
          _ = ∑ equation : Equations,
              ∑ index : Fin q × CoreRow nw nq,
                summand index equation := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro equation _
            calc
              (∑ index : Fin q × CoreRow nw nq, summand index equation) =
                  ∑ i : Fin q, ∑ blockRow : CoreRow nw nq,
                    weights equation *
                      statement.coefficient equation blockRow.1 blockRow.2 i *
                        decodedMessages D layout rows blockRow.1 blockRow.2 i := by
                simp [summand, Fintype.sum_prod_type]
              _ = ∑ blockRow : CoreRow nw nq, ∑ i : Fin q,
                    weights equation *
                      statement.coefficient equation blockRow.1 blockRow.2 i *
                        decodedMessages D layout rows blockRow.1 blockRow.2 i :=
                Finset.sum_comm
              _ = _ := by simp [Fintype.sum_sigma, mul_assoc]
      rw [hcore]
      ring

omit [DecidableEq F] in
/-- The global target check for a canonical arithmetic payload is exactly one
affine equation in the linear weights. -/
theorem targetCheck_eq_affineEquation
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (htarget : (∑ i : Fin q, (payload.arithmetic : F[X]).eval
      (D.point (logicalWitnessPosition layout i))) =
        statement.combinedTarget weights)
    (hcanonical : payload.arithmetic =
      (responseSemantics D hk hprimary layout statement weights).canonical B rows) :
    finiteDot weights (decodedLinearResidual D layout statement rows) =
      -decodedZRMaskSum D layout rows := by
  rw [hcanonical, responseCanonical_logical_sum D hk hprimary layout statement
    weights B rows] at htarget
  linear_combination htarget

/-- For a false statement, a canonical accepted payload places the auxiliary
challenge in one nontrivial affine hyperplane. -/
theorem falseLanguage_targetCheck
    [Fintype F] [DecidableEq Equations]
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (B : Challenge F (rowCount nw nq) s)
    (payload : LigeroPayload F (r + w) s)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (htarget : (∑ i : Fin q, (payload.arithmetic : F[X]).eval
      (D.point (logicalWitnessPosition layout i))) =
        statement.combinedTarget weights)
    (hcanonical : payload.arithmetic =
      (responseSemantics D hk hprimary layout statement weights).canonical B rows)
    (hproduct : ∀ row : Fin nq,
      (rows (leftIndex row) : F[X]) * (rows (rightIndex row) : F[X]) =
        (rows (outputIndex row) : F[X]))
    (hfalse : ¬statement.Language) :
    (decodedLinearResidual D layout statement rows ≠ 0) ∧
      (weights ∈ affineEquationSolutions
        (decodedLinearResidual D layout statement rows)
        (-decodedZRMaskSum D layout rows)) ∧
      Fintype.card F *
          (affineEquationSolutions
            (decodedLinearResidual D layout statement rows)
            (-decodedZRMaskSum D layout rows)).card ≤
        Fintype.card (Equations → F) := by
  have hnonzero := linearResidual_ne_zero_of_not_language D layout statement rows
    hproduct hfalse
  refine ⟨hnonzero, ?_, affineEquationSolutions_density _ _ hnonzero⟩
  simp only [affineEquationSolutions, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact targetCheck_eq_affineEquation D hk hprimary layout statement weights B
    payload rows htarget hcanonical

end LigeroFamily.PolynomialDirect
