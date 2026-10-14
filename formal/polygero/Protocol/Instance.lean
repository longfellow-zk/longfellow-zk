import polygero.Protocol.Layer
import polygero.Protocol.Verifier

/-! Concrete one-layer parameters and verifier semantics, independent of recursion. -/

namespace RecursivePolygero
open Finset Polynomial Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

structure Instance (F : Type) [Field F] where
  q : ℕ
  r : ℕ
  w : ℕ
  n : ℕ
  nw : ℕ
  nq : ℕ
  s : ℕ
  t : ℕ
  Equations : Type
  equationsFinite : Fintype Equations
  equationsDecidable : DecidableEq Equations
  domain : ReedSolomon.Domain F r w n
  layout : ConstraintLayout F q w
  primary_le : r+w+s ≤ n
  query_le : t ≤ n

attribute [instance] Instance.equationsFinite Instance.equationsDecidable

noncomputable def Instance.layer (I : Instance F) : Layer where
  Statement := ConstraintSystem F I.nw I.nq I.q I.Equations
  Witness := CoreMessages F I.nw I.nq I.q
  Oracle := Oracle F I.nw I.nq I.n
  Coin := Coin F I.Equations I.nw I.nq I.s
  Query := QuerySet I.n I.t
  Payload := LigeroPayload F (I.r+I.w) I.s
  oracleFinite := Fintype.ofInjective
    (fun W : Oracle F I.nw I.nq I.n => (W.ordinary.core, W.ordinary.checkedMask, W.proximityMask))
    (by rintro ⟨⟨a,b⟩,c⟩ ⟨⟨a',b'⟩,c'⟩ h; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl,rfl,rfl⟩; rfl)
  oracleNonempty := ⟨⟨⟨fun _ _ _ => 0, fun _ _ => 0⟩, fun _ => 0⟩⟩
  coinFinite := inferInstance
  queryFinite := inferInstance
  coinNonempty := inferInstance
  queryNonempty := QuerySet.nonempty I.query_le
  payloadFinite := inferInstance
  payloadNonempty := ⟨⟨0,0⟩⟩
  satisfies := ConstraintSystem.Satisfies
  verify σ W c p Q := verify I.domain (by have := I.primary_le; omega) I.layout σ c p Q (openOracle W Q) = true

end RecursivePolygero
