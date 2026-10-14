import polygero.Local.Candidates

/-! Agreement-sensitive deterministic recovery. Failure is an event, not an assigned score. -/
namespace RecursivePolygero.Counting
open Finset
attribute [local instance] Classical.propDecidable

def outputHit {ι : Type*} (D : ι → Prop) : Option ι → Prop
  | none => True
  | some i => D i

end RecursivePolygero.Counting
