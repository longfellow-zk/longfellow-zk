import polygero.FiatShamir.MerkleCompiler

/-!
# Typed participants in a shared column commitment

A position identifies a participant, so equal field types may occur more than
once. Witness widths and equation types remain local to each field. The four
common geometry parameters identify the shared column/query space; no field
arithmetic is converted into another field.
-/

namespace LfzkV2.Joint

open RecursivePolygero LigeroFamily

structure Participant (k s n t : ℕ) where
  Carrier : Type
  field : Field Carrier
  finite : Fintype Carrier
  eq : DecidableEq Carrier
  backend : @Instance Carrier field
  dimension : backend.r + backend.w = k
  batching : backend.s = s
  columns : backend.n = n
  openings : backend.t = t
  linearOnly : backend.nq = 0

attribute [instance] Participant.field Participant.finite Participant.eq

namespace Participant

variable {k s n t : ℕ} (P : Participant k s n t)

abbrev Statement := P.backend.layer.Statement
abbrev Witness := P.backend.layer.Witness
abbrev Oracle := P.backend.layer.Oracle
abbrev Coin := P.backend.layer.Coin
abbrev Response := P.backend.layer.Payload
abbrev Leaf := MerkleCompiler.Leaf P.Carrier P.backend.nw P.backend.nq

noncomputable def localQuery (Q : QuerySet n t) : P.backend.layer.Query :=
  cast (by change QuerySet n t = QuerySet P.backend.n P.backend.t
           rw [P.columns, P.openings]) Q

abbrev Opening (Q : QuerySet n t) :=
  RecursivePolygero.Local.Polygero.Opening P.Carrier P.backend.nw P.backend.nq
    P.backend.n P.backend.t (P.localQuery Q)

/-- Reindexing only transports the common column count. It does not change
any field value or the order of rows inside a participant. -/
noncomputable def columnsEquiv : P.Oracle ≃ (Fin n → P.Leaf) :=
  (MerkleCompiler.columnsEquiv P.Carrier P.backend.nw P.backend.nq P.backend.n).trans
    (Equiv.cast (by rw [P.columns]))

noncomputable def compiler (ht : 0 < t) :
    Bcs.Compiler P.Statement P.Oracle P.Coin P.Response (QuerySet n t) P.Opening P.Leaf n := by
  rcases P with ⟨F, hF, hfin, hdec, I, hk, hs, hn, htEq, hlinear⟩
  cases hn
  cases htEq
  exact MerkleCompiler.compiler I ht

theorem compiler_columns (ht : 0 < t) : (P.compiler ht).columns = P.columnsEquiv := by
  rcases P with ⟨F, hF, hfin, hdec, I, hk, hs, hn, htEq, hlinear⟩
  cases hn
  cases htEq
  rfl

theorem compiler_indices (ht : 0 < t) (Q : QuerySet n t) :
    (P.compiler ht).indices Q = Q.coordinates := by
  rcases P with ⟨F, hF, hfin, hdec, I, hk, hs, hn, htEq, hlinear⟩
  cases hn
  cases htEq
  rfl

theorem compiler_verify (ht : 0 < t) (σ : P.Statement) (W : P.Oracle)
    (coin : P.Coin) (response : P.Response) (Q : QuerySet n t) :
    (P.compiler ht).protocol.verify σ coin response Q
      ((P.compiler ht).protocol.openOracle W Q) = true ↔
      P.backend.layer.verify σ W coin response (P.localQuery Q) := by
  rcases P with ⟨F, hF, hfin, hdec, I, hk, hs, hn, htEq, hlinear⟩
  cases hn
  cases htEq
  rfl

end Participant
end LfzkV2.Joint
