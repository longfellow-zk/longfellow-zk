import polygero.Protocol.Verifier
import polygero.Local.LegacyCandidateTests
import LigeroFamily.Soundness.Hypergeometric

/-! Single-candidate arithmetic for the masked verifier. -/
namespace RecursivePolygero.Local.Polygero
open Polynomial Finset Codes LigeroFamily MultiplicativeCode
open LigeroFamily.PolynomialDirect
variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {q r w n nw nq s A H openings : ℕ}
variable (D : ReedSolomon.Domain F r w n) (hk : r+w ≤ n) (hprimary : r+w+s ≤ n)
variable (layout : ConstraintLayout F q w) (statement : ConstraintSystem F nw nq q Equations)
/-- Candidates contain exactly the physical ordinary rows. -/
noncomputable def candidateTests (f : Fin (rowCount nw nq) → DegreeLT F (r+w)) :=
  ListSoundness.candidateTests D layout statement (extendRows f)

theorem candidateTests_card (f : Fin (rowCount nw nq) → DegreeLT F (r+w))
    (hfalse : ¬statement.Language) :
    (candidateTests D layout statement f).card * Fintype.card F ≤ Fintype.card (Equations → F) :=
  ListSoundness.candidateTests_card D layout statement (extendRows f) hfalse

theorem candidateTests_of_checks (weights : Equations → F)
    (payload : LigeroPayload F (r+w) s)
    (f : Fin (rowCount nw nq) → DegreeLT F (r+w))
    (hglobal : globalCheck D layout statement weights payload)
    (hcanonical : payload.arithmetic =
      (responseSemantics D hk hprimary layout statement weights).canonical 0 f)
    (hproducts : ∀ row : Fin nq, (f (leftIndex row) : F[X]) * (f (rightIndex row) : F[X]) =
      (f (outputIndex row) : F[X])) :
    weights ∈ candidateTests D layout statement f := by
  have hp : ∀ row : Fin nq,
      (extendRows (V := DegreeLT F (r+w)) (nw := nw) f (PolynomialDirect.leftIndex row) : F[X]) *
        (extendRows (V := DegreeLT F (r+w)) (nw := nw) f (PolynomialDirect.rightIndex row) : F[X]) =
        (extendRows (V := DegreeLT F (r+w)) (nw := nw) f (PolynomialDirect.outputIndex row) : F[X]) := by
    simpa only [PolynomialDirect.leftIndex, PolynomialDirect.rightIndex,
      PolynomialDirect.outputIndex, extendRows_core, leftIndex, rightIndex, outputIndex] using hproducts
  have ht := PolynomialDirect.targetCheck_eq_affineEquation D hk hprimary layout statement
    weights 0 payload (extendRows f) hglobal hcanonical
  simpa only [candidateTests, ListSoundness.candidateTests, if_pos hp,
    affineEquationSolutions, mem_filter, mem_univ, true_and] using ht

end RecursivePolygero.Local.Polygero
