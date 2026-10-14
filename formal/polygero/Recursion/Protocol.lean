import polygero.Reduction.ChildInstance
import polygero.Recursion.Execution

/-! Concrete recursive Polygero protocols and their execution chains. -/

namespace RecursivePolygero
open Finset Polynomial Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

inductive Protocol : Instance F → Type 1
  | terminal (I : Instance F) : Protocol I
  | step {I : Instance F} (child : Child I) (tail : Protocol child.instance) : Protocol I

noncomputable def Protocol.chain {I : Instance F} : Protocol I → Chain I.layer
  | .terminal I => .terminal I.layer
  | .step child tail => .step child.link tail.chain

end RecursivePolygero
