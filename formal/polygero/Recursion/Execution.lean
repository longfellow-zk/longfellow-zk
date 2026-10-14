import polygero.Recursion.Chain

/-! The Boolean recursive verifier on its complete finite verifier sequence. -/

namespace RecursivePolygero
attribute [local instance] Classical.propDecidable

def Chain.Coins {L : Layer} : Chain L → Type
  | .terminal L => L.Coin × L.Query
  | .step _ tail => (L.Coin × L.Query) × tail.Coins

noncomputable instance Chain.coinsFinite {L : Layer} (chain : Chain L) : Fintype chain.Coins :=
  match chain with
  | .terminal L => inferInstanceAs (Fintype (L.Coin × L.Query))
  | .step (L := L) _ tail =>
    letI := Chain.coinsFinite tail
    inferInstanceAs (Fintype ((L.Coin × L.Query) × tail.Coins))

instance Chain.coinsNonempty {L : Layer} (chain : Chain L) : Nonempty chain.Coins := by
  induction chain with
  | terminal L => exact inferInstanceAs (Nonempty (L.Coin × L.Query))
  | step link tail ih =>
    letI := ih
    exact inferInstanceAs (Nonempty ((_ × _) × tail.Coins))

noncomputable def executionVerify {L : Layer} (chain : Chain L) (σ : L.Statement)
    (W : L.Oracle) (p : Strategy chain) (coins : chain.Coins) : Bool :=
  match chain with
  | .terminal L => decide (L.verify σ W coins.1 (p coins.1) coins.2)
  | .step link tail => decide (link.direct W coins.1.2) &&
      executionVerify tail (link.statement σ W coins.1.1 coins.1.2)
        (p.1 coins.1.1) (p.2 coins.1.1 coins.1.2) coins.2

end RecursivePolygero
