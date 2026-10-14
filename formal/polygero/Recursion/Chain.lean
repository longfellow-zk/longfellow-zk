import polygero.Reduction.Link

/-! Recursive chains and the timing of adaptive prover messages. -/

namespace RecursivePolygero
open Finset
attribute [local instance] Classical.propDecidable

inductive Chain : Layer → Type 1
  | terminal (L : Layer) : Chain L
  | step {L M : Layer} (link : Link L M) (tail : Chain M) : Chain L

/-- Allowed message choices as functions of the preceding verifier messages.
All bounds quantify over these functions and count verifier sequences. -/
def Strategy {L : Layer} : Chain L → Type
  | .terminal L => L.Coin → L.Payload
  | .step (M := M) _ tail =>
      (L.Coin → M.Oracle) × (L.Coin → L.Query → Strategy tail)

end RecursivePolygero
