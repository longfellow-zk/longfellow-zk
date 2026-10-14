import polygero.Recursion.Execution

/-! The recorded execution path supplied to a transcript-assisted extractor. -/
namespace RecursivePolygero.Counting

/-- The actual path, including each child oracle and the terminal response. -/
def _root_.RecursivePolygero.Chain.Transcript {L : Layer} : Chain L → Type
  | .terminal L => L.Coin × L.Query × L.Payload
  | .step (M := M) _ tail => L.Coin × L.Query × M.Oracle × tail.Transcript

noncomputable def _root_.RecursivePolygero.Chain.record {L : Layer} (chain : Chain L)
    (messages : Strategy chain) (coins : chain.Coins) : chain.Transcript :=
  match chain with
  | .terminal _ => (coins.1, coins.2, messages coins.1)
  | .step _ tail => (coins.1.1, coins.1.2, messages.1 coins.1.1,
      tail.record (messages.2 coins.1.1 coins.1.2) coins.2)

end RecursivePolygero.Counting
