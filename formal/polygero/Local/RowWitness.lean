import polygero.Protocol.Verifier
import polygero.Local.LegacyArithmetic

namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily Local Local.Polygero
variable {F Equations : Type} [Field F] {q r w n nw nq : ℕ}
variable {D : ReedSolomon.Domain F r w n}

/-- The logical witness obtained by evaluating the fixed ordinary-row tuple. -/
noncomputable def rowWitness (layout : ConstraintLayout F q w)
    (f : Fin (rowCount nw nq) → DegreeLT F (r+w)) : CoreMessages F nw nq q :=
  PolynomialDirect.decodedMessages D layout (extendRows f)

end RecursivePolygero
