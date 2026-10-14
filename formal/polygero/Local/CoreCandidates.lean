import polygero.Local.Candidates
import polygero.Protocol.Instance
import polygero.Local.CoreRows

/-! Interfaces from the proved local Polygero bounds to the counting induction.
The recursive proof uses exact normalized counts. -/
namespace RecursivePolygero.Counting
open Finset Polynomial Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- All polynomial witness tuples. The extractor does not enumerate this family. -/
noncomputable def tupleCounts (I : Instance F) : Candidates I.layer where
  Index := Fin (Fintype.card (CoreRow I.nw I.nq)) → DegreeLT F (I.r+I.w)
  finiteIndex := inferInstance
  witness g := I.coreWitness g

end RecursivePolygero.Counting
