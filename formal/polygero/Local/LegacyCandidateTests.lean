import polygero.Local.LegacyArithmetic

/-! Arithmetic counting for one fixed tuple of polynomial rows. -/
namespace LigeroFamily.PolynomialDirect.ListSoundness
open Finset Polynomial RecursivePolygero.Local MultiplicativeCode
variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {q r w n nw nq : ℕ}
variable (D : ReedSolomon.Domain F r w n)
variable (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
noncomputable def candidateTests (f : Fin (rowCount nw nq) → DegreeLT F (r + w)) :
    Finset (Equations → F) := by
  classical
  exact if ∀ row : Fin nq, (f (leftIndex row) : F[X]) * (f (rightIndex row) : F[X]) =
      (f (outputIndex row) : F[X]) then
    affineEquationSolutions (decodedLinearResidual D layout statement f)
      (-decodedZRMaskSum D layout f) else ∅

theorem candidateTests_card (f : Fin (rowCount nw nq) → DegreeLT F (r + w))
    (hfalse : ¬statement.Language) :
    (candidateTests D layout statement f).card * Fintype.card F ≤ Fintype.card (Equations → F) := by
  classical
  unfold candidateTests
  split_ifs with hp
  · simpa [mul_comm] using affineEquationSolutions_density
      (decodedLinearResidual D layout statement f) (-decodedZRMaskSum D layout f)
      (linearResidual_ne_zero_of_not_language D layout statement f hp hfalse)
  · simp

end LigeroFamily.PolynomialDirect.ListSoundness
