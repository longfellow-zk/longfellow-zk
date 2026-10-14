import polygero.Protocol.Layer

/-! A satisfaction-preserving link between two protocol layers. -/

namespace RecursivePolygero
open Finset
attribute [local instance] Classical.propDecidable

structure Link (L M : Layer) where
  decode : M.Witness → L.Payload
  statement : L.Statement → L.Oracle → L.Coin → L.Query → M.Statement
  direct : L.Oracle → L.Query → Prop
  sound : ∀ σ W c Q w, direct W Q → M.satisfies (statement σ W c Q) w →
    L.verify σ W c (decode w) Q

end RecursivePolygero
