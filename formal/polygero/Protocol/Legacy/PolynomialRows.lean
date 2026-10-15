import LigeroFamily.Protocol.DirectProduct
import LigeroFamily.Code.ReedSolomon
import polygero.Protocol.SharedColumn

/-! Compatibility row coordinates for reused masked-arithmetic lemmas.
The physical tableau is defined separately in `Protocol/Tableau.lean`. Its
`extendRows` adapter supplies the extra coordinate as zero, without another
committed word or sampled challenge. -/

namespace LigeroFamily.PolynomialDirect
open Finset Polynomial
open MultiplicativeCode
open RecursivePolygero.Local
variable {F Equations : Type*} [Field F] [DecidableEq F]
variable [Fintype Equations]
variable {q r w n nw nq s : Nat}

/-- Legacy arithmetic coordinates. The physical row adapter supplies the extra
coordinate as zero; this is not the protocol challenge space. -/
abbrev BatchedRow (nw nq : Nat) :=
  SchemeTestedRow LinearConstraintMask nw nq 1 ⊕ Unit

abbrev rowCount (nw nq : Nat) := Fintype.card (BatchedRow nw nq)

noncomputable def rowEquiv (nw nq : Nat) :
    Fin (rowCount nw nq) ≃ BatchedRow nw nq :=
  (Fintype.equivFin (BatchedRow nw nq)).symm

noncomputable def indexOf (row : BatchedRow nw nq) : Fin (rowCount nw nq) :=
  (rowEquiv nw nq).symm row

@[simp] theorem rowEquiv_indexOf (row : BatchedRow nw nq) :
    rowEquiv nw nq (indexOf row) = row := by
  simp [indexOf]

noncomputable def coreIndex (block : CoreBlock)
    (row : Fin (block.rowCount nw nq)) : Fin (rowCount nw nq) :=
  indexOf (Sum.inl (Sum.inl ⟨block, row⟩))

noncomputable def maskIndex (kind : LinearConstraintMask) :
    Fin (rowCount nw nq) :=
  indexOf (Sum.inl (Sum.inr (0, kind)))

noncomputable def blindIndex : Fin (rowCount nw nq) :=
  indexOf (Sum.inr ())

/-- The ordinary RS code on committed columns, with the larger primary
response dimension `r+w+s`. -/
def primaryCode (D : ReedSolomon.Domain F r w n) (hprimary : r + w + s ≤ n) :
    Codes.RSCode F n (r + w + s) where
  node j := D.point (codePosition j)
  node_injective := fun _ _ h => by
    simpa [codePosition] using D.injective h
  dimension_le_length := hprimary

/-- Turn a bounded polynomial into its full Ligero evaluation row. -/
noncomputable def evaluationRow (D : ReedSolomon.Domain F r w n)
    {degree : Nat} (p : DegreeLT F degree) : EvaluationRow F r w n :=
  fun position => (p : F[X]).eval (D.point position)

omit [DecidableEq F] in
theorem evaluationRow_mem (D : ReedSolomon.Domain F r w n)
    {degree : Nat} (p : DegreeLT F degree) :
    evaluationRow D p ∈ ReedSolomon.evaluationSpace D degree :=
  (ReedSolomon.mem_evaluationSpace D).mpr ⟨p, p.2, fun _ => rfl⟩

/-- Choose the unique degree-bounded polynomial represented by a concrete
response row. -/
noncomputable def responsePolynomial
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (row : EvaluationRow F r w n)
    (hrow : row ∈ (ReedSolomon.multiplicativeCode D hk).response) :
    DegreeLT F (2 * (r + w)) :=
  ⟨Classical.choose ((ReedSolomon.mem_evaluationSpace D).mp hrow),
    (Classical.choose_spec ((ReedSolomon.mem_evaluationSpace D).mp hrow)).1⟩

omit [DecidableEq F] in
theorem responsePolynomial_eval
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (row : EvaluationRow F r w n)
    (hrow : row ∈ (ReedSolomon.multiplicativeCode D hk).response)
    (position : Position r w n) :
    ((responsePolynomial D hk row hrow : DegreeLT F (2 * (r + w))) : F[X]).eval
        (D.point position) = row position := by
  classical
  exact ((Classical.choose_spec
    ((ReedSolomon.mem_evaluationSpace D).mp hrow)).2 position).symm

noncomputable def decodedCore (D : ReedSolomon.Domain F r w n)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (block : CoreBlock) (row : Fin (block.rowCount nw nq)) :
    EvaluationRow F r w n :=
  evaluationRow D (rows (coreIndex block row))

noncomputable def decodedMask (D : ReedSolomon.Domain F r w n)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (kind : LinearConstraintMask) : EvaluationRow F r w n :=
  evaluationRow D (rows (maskIndex kind))

noncomputable def linearRow
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w)) :
    EvaluationRow F r w n :=
  DirectVerifier.linearResponse (ReedSolomon.multiplicativeCode D hk)
    (ReedSolomon.maskingBasis D hk) layout statement weights
    (decodedCore D rows) (decodedMask D rows)

omit [DecidableEq F] in
theorem linearRow_mem
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F)
    (rows : Fin (rowCount nw nq) → DegreeLT F (r + w)) :
    linearRow D hk layout statement weights rows ∈
      (ReedSolomon.multiplicativeCode D hk).response := by
  classical
  unfold linearRow DirectVerifier.linearResponse
  apply Submodule.add_mem
  · unfold DirectVerifier.linearCore
    apply Submodule.sum_mem
    intro block _
    apply Submodule.sum_mem
    intro row _
    apply (ReedSolomon.multiplicativeCode D hk).mul_mem
    · exact (ReedSolomon.multiplicativeCode D hk).encode_mem _ _
    · exact evaluationRow_mem D _
  · unfold DirectVerifier.linearMask
    apply Submodule.add_mem
    · exact (ReedSolomon.maskingBasis D hk).vanishing_mul_mem
        (evaluationRow_mem D _)
    · apply (ReedSolomon.multiplicativeCode D hk).mul_mem
      · exact (ReedSolomon.multiplicativeCode D hk).zR_mem
      · exact evaluationRow_mem D _

end LigeroFamily.PolynomialDirect
