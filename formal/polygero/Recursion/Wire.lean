import polygero.Protocol.Wire
import polygero.Recursion.Protocol

/-! Adaptive recursive wire strategies and their exact verifier expansion. -/

namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Child commitments contain core rows only and still precede parent queries. -/
def Protocol.WireStrategy {I : Instance F} : Protocol I → Type
  | .terminal I => I.layer.Coin → I.layer.Payload
  | .step (I := I) child tail =>
      (I.layer.Coin → child.instance.WireOracle false) ×
      (I.layer.Coin → I.layer.Query → tail.WireStrategy)

noncomputable def Protocol.expandWireStrategy {I : Instance F} (P : Protocol I) :
    P.WireStrategy → Strategy P.chain :=
  match P with
  | .terminal _ => id
  | .step child tail => fun p =>
      ⟨fun c => child.instance.expandWireOracle false (p.1 c), fun c Q => tail.expandWireStrategy (p.2 c Q)⟩

noncomputable def Protocol.wireVerify {I : Instance F} (P : Protocol I) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks) (p : P.WireStrategy) (coins : P.chain.Coins) : Bool :=
  executionVerify P.chain σ (I.expandWireOracle masks W) (P.expandWireStrategy p) coins

/-- Soundness is inherited by exact substitution into the concrete verifier. -/
theorem Protocol.wireVerify_eq {I : Instance F} (P : Protocol I) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks) (p : P.WireStrategy) (coins : P.chain.Coins) :
    P.wireVerify masks σ W p coins =
      executionVerify P.chain σ (I.expandWireOracle masks W) (P.expandWireStrategy p) coins := rfl

end RecursivePolygero
