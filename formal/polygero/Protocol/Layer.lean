import Mathlib.Tactic

/-! One invocation: statement, witness, oracle, challenges, and verifier. -/

namespace RecursivePolygero
open Finset
attribute [local instance] Classical.propDecidable

structure Layer where
  Statement : Type
  Witness : Type
  Oracle : Type
  Coin : Type
  Query : Type
  Payload : Type
  oracleFinite : Fintype Oracle
  oracleNonempty : Nonempty Oracle
  coinFinite : Fintype Coin
  queryFinite : Fintype Query
  coinNonempty : Nonempty Coin
  queryNonempty : Nonempty Query
  payloadFinite : Fintype Payload
  payloadNonempty : Nonempty Payload
  satisfies : Statement → Witness → Prop
  verify : Statement → Oracle → Coin → Payload → Query → Prop

attribute [instance] Layer.coinFinite Layer.queryFinite Layer.coinNonempty Layer.queryNonempty
  Layer.payloadFinite Layer.payloadNonempty Layer.oracleFinite Layer.oracleNonempty

end RecursivePolygero
