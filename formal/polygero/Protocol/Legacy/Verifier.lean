import polygero.Protocol.Legacy.PolynomialRows

/-! Arithmetic compatibility adapter for the physical Polygero rows.
The extra legacy row coordinate is supplied as zero by `extendRows`; this file
defines no alternate oracle or acceptance predicate. -/

namespace LigeroFamily.PolynomialDirect
open Finset Polynomial
open MultiplicativeCode
open RecursivePolygero.Local
variable {F Equations : Type*} [Field F] [DecidableEq F]
variable [Fintype Equations]
variable {q r w n nw nq s : Nat}

/-- Masked-linear local equation, evaluated at one committed
column. -/
noncomputable def linearPointwise
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) (z : Fin n)
    (values : Fin (rowCount nw nq) → F) : F :=
  (∑ block : CoreBlock, ∑ row : Fin (block.rowCount nw nq),
      DirectVerifier.coefficientRow (ReedSolomon.multiplicativeCode D hk)
          layout statement weights block row (codePosition z) *
        values (coreIndex block row)) +
    (ReedSolomon.maskingBasis D hk).vanishing (codePosition z) *
      values (maskIndex .vCoefficient) +
    (ReedSolomon.multiplicativeCode D hk).zR (codePosition z) *
      values (maskIndex .zRCoefficient)

/-- The arithmetic polynomial semantics used by the physical Polygero verifier.
Polynomial challenges affect the primary response; independent linear weights
determine this arithmetic response. -/
noncomputable def responseSemantics
    (D : ReedSolomon.Domain F r w n) (hk : r + w ≤ n)
    (hprimary : r + w + s ≤ n)
    (layout : ConstraintLayout F q w)
    (statement : ConstraintSystem F nw nq q Equations)
    (weights : Equations → F) :
    ResponseSemantics (primaryCode D hprimary) (rowCount nw nq)
      (r + w) s (2 * (r + w)) where
  pointwise _B z values := linearPointwise D hk layout statement weights z values
  canonical _B rows := responsePolynomial D hk
    (linearRow D hk layout statement weights rows)
    (linearRow_mem D hk layout statement weights rows)
  canonical_eval := by
    intro B rows z
    change ((responsePolynomial D hk
      (linearRow D hk layout statement weights rows)
      (linearRow_mem D hk layout statement weights rows) :
        DegreeLT F (2 * (r + w))) : F[X]).eval
          (D.point (codePosition z)) = _
    rw [responsePolynomial_eval D hk _ _ (codePosition z)]
    simp only [linearPointwise, linearRow, DirectVerifier.linearResponse,
      DirectVerifier.linearCore, DirectVerifier.linearMask, Pi.add_apply,
      Finset.sum_apply, rowMul_apply, decodedCore, decodedMask, evaluationRow]
    simp only [primaryCode]
    ring

noncomputable def leftIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .left row

noncomputable def rightIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .right row

noncomputable def outputIndex (row : Fin nq) : Fin (rowCount nw nq) :=
  coreIndex .output row

end LigeroFamily.PolynomialDirect
