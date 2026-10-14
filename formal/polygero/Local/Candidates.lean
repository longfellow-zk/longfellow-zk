import polygero.Protocol.Layer
import polygero.Algebra.FiniteProbability

/-! Finite match families and counts of concrete verifier sequences.
All averages below are exact finite sums divided by cardinalities. -/
namespace RecursivePolygero.Counting
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def responseCount (L : Layer) (σ : L.Statement) (W : L.Oracle)
    (c : L.Coin) (p : L.Payload) : ℕ := (univ.filter (L.verify σ W c p)).card

structure Candidates (L : Layer) where
  Index : Type
  finiteIndex : Fintype Index
  witness : Index → L.Witness

attribute [instance] Candidates.finiteIndex

end RecursivePolygero.Counting
