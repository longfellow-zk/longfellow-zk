import polygero.Local.GrindingAlgebra

/-! Unmasked honest completion for a linear child instance. The committed
oracle depends only on its witness and the public encoding parameters; it
can therefore be fixed before the parent query determines the child
statement. Canonical payloads subsequently depend on that statement and
the child coin. -/

namespace RecursivePolygero.ProfileAnalysis.HonestCompletion

open Polynomial Finset Codes LigeroFamily Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def encodedRow (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq)) :=
  (ReedSolomon.multiplicativeCode I.domain (by have := I.primary_le; omega)).encode
    0 (I.layout.extend (witness block row))

private theorem encodedRow_mem (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq)) :
    encodedRow I witness block row ∈ ReedSolomon.evaluationSpace I.domain (I.r + I.w) :=
  (ReedSolomon.multiplicativeCode I.domain (by have := I.primary_le; omega)).encode_mem _ _

/-- Polynomial representative of a witness row with deterministic zero
random padding. Its definition does not inspect a statement or a coin. -/
noncomputable def corePolynomial (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq)) : DegreeLT F (I.r + I.w) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace I.domain).mp
      (encodedRow_mem I witness block row)),
    (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp
      (encodedRow_mem I witness block row))).1⟩

theorem corePolynomial_eval (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq))
    (position : Position I.r I.w I.n) :
    (corePolynomial I witness block row : F[X]).eval (I.domain.point position) =
      encodedRow I witness block row position :=
  ((Classical.choose_spec ((ReedSolomon.mem_evaluationSpace I.domain).mp
    (encodedRow_mem I witness block row))).2 position).symm

@[simp] theorem corePolynomial_logical (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq)) (i : Fin I.q) :
    (corePolynomial I witness block row : F[X]).eval
      (I.domain.point (logicalWitnessPosition I.layout i)) = witness block row i := by
  rw [corePolynomial_eval]
  simp [encodedRow, logicalWitnessPosition, I.layout.extend_logical]

/-- The actual core-only transmitted oracle. It is common to every child
statement satisfied by this witness. -/
noncomputable def wireOracle (I : Instance F) (witness : I.layer.Witness) : I.WireOracle false :=
  fun row j => (corePolynomial I witness row.1 row.2 : F[X]).eval
    ((primaryCode I.domain I.primary_le).node j)

noncomputable def rows (I : Instance F) (witness : I.layer.Witness) :
    Fin (rowCount I.nw I.nq) → DegreeLT F (I.r + I.w) := fun i =>
  match rowEquiv I.nw I.nq i with
  | .inl row => corePolynomial I witness row.1 row.2
  | .inr _ => 0

@[simp] theorem rows_core (I : Instance F) (witness : I.layer.Witness)
    (block : CoreBlock) (row : Fin (block.rowCount I.nw I.nq)) :
    rows I witness (coreIndex block row) = corePolynomial I witness block row := by
  simp [rows, coreIndex]

@[simp] theorem rows_mask (I : Instance F) (witness : I.layer.Witness)
    (kind : LinearConstraintMask) : rows I witness (maskIndex kind) = 0 := by
  simp [rows, maskIndex]

theorem rows_decode (I : Instance F) (witness : I.layer.Witness) :
    PolynomialDirect.decodedMessages I.domain I.layout (extendRows (rows I witness)) = witness := by
  funext block row i
  simp [PolynomialDirect.decodedMessages]

theorem rows_zero_residual (I : Instance F) (witness : I.layer.Witness)
    (sigma : I.layer.Statement) (hsat : I.layer.satisfies sigma witness) :
    PolynomialDirect.decodedLinearResidual I.domain I.layout sigma (extendRows (rows I witness)) = 0 := by
  funext e
  simp only [PolynomialDirect.decodedLinearResidual, rows_decode, Pi.zero_apply]
  exact sub_eq_zero.mpr (hsat.1 e)

theorem rows_zero_mask (I : Instance F) (witness : I.layer.Witness) :
    PolynomialDirect.decodedZRMaskSum I.domain I.layout (extendRows (rows I witness)) = 0 := by
  simp [PolynomialDirect.decodedZRMaskSum]

theorem oracleWords_agree (I : Instance F) (witness : I.layer.Witness)
    (i : Fin (rowCount I.nw I.nq)) (j : Fin I.n) :
    oracleWords (I.expandWireOracle false (wireOracle I witness)).ordinary i j =
      (rows I witness i : F[X]).eval ((primaryCode I.domain I.primary_le).node j) := by
  unfold oracleWords rows
  cases rowEquiv I.nw I.nq i with
  | inl row => rfl
  | inr kind => simp [Instance.expandWireOracle]

/-- A fixed witness has a fixed commitment, even when the child statement
is chosen only after the parent query. Every subsequent child coin has a
canonical payload accepted at every terminal query. `nq = 0` is the actual
linear coefficient-child interface. -/
theorem verify_all_queries (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (hnq : I.nq = 0) (witness : I.layer.Witness)
    (sigma : I.layer.Statement) (hsat : I.layer.satisfies sigma witness)
    (coin : I.layer.Coin) (Q : I.layer.Query) :
    I.layer.verify sigma (I.expandWireOracle false (wireOracle I witness)) coin
      (GrindingAlgebra.canonicalPayload I hk sigma coin (rows I witness)) Q := by
  apply GrindingAlgebra.canonicalPayload_accepts I hk sigma _ coin (rows I witness) Q
  · rw [rows_zero_residual I witness sigma hsat, rows_zero_mask]
    simp [finiteDot]
  · intro j _
    rfl
  · intro i j _
    exact oracleWords_agree I witness i j
  · intro g
    have := g.isLt
    omega

/-- Entry variation gives different real commitments while retaining
completion on every terminal query avoiding the changed coordinate. -/
theorem varied_verify_avoiding (I : Instance F) (hk : 1 ≤ I.r + I.w)
    (hnq : I.nq = 0) (witness : I.layer.Witness)
    (sigma : I.layer.Statement) (hsat : I.layer.satisfies sigma witness)
    (coin : I.layer.Coin) (Q : I.layer.Query) (row : I.WireRow false)
    (col : Fin I.n) (c : F) (havoid : col ∉ Q.coordinates) :
    I.layer.verify sigma
      (I.expandWireOracle false (varyWireEntry I (wireOracle I witness) row col c)) coin
      (GrindingAlgebra.canonicalPayload I hk sigma coin (rows I witness)) Q := by
  exact (varyWireEntry_verify_iff I sigma (wireOracle I witness) row col c coin _ Q havoid).mpr
    (verify_all_queries I hk hnq witness sigma hsat coin Q)

/-- This child commitment is fixed as soon as the parent payload is fixed.
The parent query does not occur in its definition. -/
noncomputable def packedWireOracle {I : Instance F} (child : Child I)
    (payload : I.layer.Payload) : child.instance.WireOracle false :=
  wireOracle child.instance (unflatten (pack child.packing payload))

/-- Every parent query accepting a fixed payload admits perfect honest
completion under the same previously fixed child commitment. -/
theorem packed_response_verify_all {I : Instance F} (child : Child I)
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (payload : I.layer.Payload) (Q : I.layer.Query)
    (hv : I.layer.verify sigma W coin payload Q)
    (childCoin : child.instance.layer.Coin) (terminalQuery : child.instance.layer.Query) :
    child.instance.layer.verify (child.link.statement sigma W coin Q)
      (child.instance.expandWireOracle false (packedWireOracle child payload)) childCoin
      (GrindingAlgebra.canonicalPayload child.instance hk
        (child.link.statement sigma W coin Q) childCoin
        (rows child.instance (unflatten (pack child.packing payload)))) terminalQuery :=
  verify_all_queries child.instance hk rfl _ _
    (GrindingAlgebra.packed_child_satisfies child sigma W coin payload Q hv) childCoin terminalQuery

end RecursivePolygero.ProfileAnalysis.HonestCompletion
