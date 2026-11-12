import LfzkV2.Current.CellLayout
import LfzkV2.Current.ZkJoint

/-! The concrete affine-statement handoff.  Runtime equations are an ordered
vector, so their index type is `Fin count`, with no arbitrary enumeration of
an abstract finite type.  Public capacity checks construct cell addresses;
the statement compiler checks the completed row counts and appends both
fingerprint equations.  No row-equivalence certificate is supplied by a caller.

The circuit and packing relations are those already constructed by the
application decoder.  Transcript readers still have to supply the actual
fingerprint coefficients and bound responses. -/
noncomputable section
namespace LfzkV2.Current
open Application RecursivePolygero WitnessSelection
open scoped Classical

namespace Application.FieldBackend
variable {F : Type} [Field F] {k s n t : ℕ}

/-- Specialize only the public equation index.  Every coding, cell and mask
parameter is retained, and coin coordinates now follow the runtime row order. -/
def indexed (P : FieldBackend F k s n t) (count : ℕ) : FieldBackend F k s n t where
  backend := { P.backend with
    Equations := Fin count
    equationsFinite := inferInstance
    equationsDecidable := inferInstance }
  dimension := P.dimension
  batching := P.batching
  columns := P.columns
  openings := P.openings
  linearOnly := P.linearOnly

end Application.FieldBackend

namespace StatementCompiler
variable {B N : Type} [Field B] [Field N]
variable {k s n t cellsB remaining padsN : ℕ}

/-- These are public addresses, constructed once from numerical capacities.
The prime order is other inputs, hiding scalar, pads, then fingerprint masks;
the shared input prefix has no address in this participant. -/
structure Addresses (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
    (cellsB remaining padsN : ℕ) where
  binary : Fin (cellsB+2) ↪ (Fin P.backend.nw × Fin P.backend.q)
  prime : (CellLayout.Prime.Other remaining padsN ⊕ Unit) ↪
    (Fin R.backend.nw × Fin R.backend.q)

def addresses (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
    (cellsB remaining padsN : ℕ) : Option (Addresses P R cellsB remaining padsN) :=
  if h : 0 < P.backend.q ∧ cellsB+2 ≤ P.backend.nw*P.backend.q ∧
      0 < R.backend.q ∧ CellLayout.Prime.cells remaining padsN+2 ≤ R.backend.nw*R.backend.q then
    some {
      binary := CellLayout.primary h.1 h.2.1
      prime := (CellLayout.Prime.index remaining padsN).toEmbedding.trans
        (CellLayout.primary h.2.2.1 h.2.2.2) }
  else none

/-- The equality check preserves coordinate order: accepted indices are
transported by their numerical value, rather than an unspecified permutation. -/
def equationIndex (count length : ℕ) : Option (Fin count ≃ Fin length) :=
  if h : count = length then some (finCongr h) else none

theorem equationIndex_value (count length : ℕ) (index : Fin count)
    (equivalence : Fin count ≃ Fin length)
    (h : equationIndex count length = some equivalence) :
    (equivalence index).val = index.val := by
  unfold equationIndex at h
  split_ifs at h with heq
  · cases Option.some.inj h
    rfl

variable {I J PadB C : Type} [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
  [Fintype I] [DecidableEq I] [Fintype J]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]
variable (P : FieldBackend B k s n t) (R : FieldBackend (ZMod p) k s n t)
variable (A : System B I J (Fin (cellsB+2)) PadB (CellLayout.Prime.Other remaining padsN)
  (Fin padsN) (Fin cellsB) (Fin (CellLayout.Prime.cells remaining padsN)) C C p shared maskBits M K)

/-- Construct the exact final statement. Shape mismatches reject; both mask
cells and both fingerprint rows are mandatory in every successful branch. -/
def compile (layout : Addresses P R cellsB remaining padsN) (countB countN : ℕ)
    (coinsB : Coins B (Fin cellsB))
    (coinsN : Coins (ZMod p) (Fin (CellLayout.Prime.cells remaining padsN)))
    (targetB : B × B) (targetN : ZMod p × ZMod p) :
    Option (StatementData A (P.indexed countB) (R.indexed countN)) := do
  let equationsB ← equationIndex countB
    (A.binary.rows ++ FingerprintRows.rows (fun i => A.binaryLayout (.inl i))
      (fun j => A.binaryLayout (.inr j)) coinsB targetB).length
  let equationsN ← equationIndex countN
    (A.primeRows ++ FingerprintRows.rows (fun i => A.primeLayout (.inl i))
      (fun j => A.primeLayout (.inr j)) coinsN targetN).length
  pure {
    primaryB := layout.binary
    primaryN := layout.prime
    coinsB := coinsB
    coinsN := coinsN
    targetB := targetB
    targetN := targetN
    equationsB := equationsB
    equationsN := equationsN }

theorem compile_fields (layout : Addresses P R cellsB remaining padsN) (countB countN : ℕ)
    (coinsB : Coins B (Fin cellsB))
    (coinsN : Coins (ZMod p) (Fin (CellLayout.Prime.cells remaining padsN)))
    (targetB : B × B) (targetN : ZMod p × ZMod p)
    (result : StatementData A (P.indexed countB) (R.indexed countN))
    (h : compile P R A layout countB countN coinsB coinsN targetB targetN = some result) :
    result.primaryB = layout.binary ∧ result.primaryN = layout.prime ∧
      result.coinsB = coinsB ∧ result.coinsN = coinsN ∧
      result.targetB = targetB ∧ result.targetN = targetN := by
  unfold compile at h
  cases hb : equationIndex countB
      (A.binary.rows ++ FingerprintRows.rows (fun i => A.binaryLayout (.inl i))
        (fun j => A.binaryLayout (.inr j)) coinsB targetB).length with
  | none => simp only [hb] at h; contradiction
  | some equationsB =>
      simp only [hb] at h
      cases hn : equationIndex countN
          (A.primeRows ++ FingerprintRows.rows (fun i => A.primeLayout (.inl i))
            (fun j => A.primeLayout (.inr j)) coinsN targetN).length with
      | none => simp only [hn] at h; contradiction
      | some equationsN =>
          simp only [hn, pure] at h
          cases h
          exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Use the same physical maps for early witness selection and late affine
authentication. The layouts here are public addresses, with no oracle or
fingerprint challenge in the definition of the projected cells. -/
def selected (layout : Addresses P R cellsB remaining padsN)
    (countB countN cutoffB cutoffN : ℕ) {Key : Type}
    (binaryLayout : (Fin cellsB ⊕ Fin 2) ≃ Fin (cellsB+2))
    (primeLayout : (Fin (CellLayout.Prime.cells remaining padsN) ⊕ Fin 2) ≃
      (CellLayout.Prime.Other remaining padsN ⊕ Unit)) :
    ZkJoint.JointParam (P.indexed countB).participant (R.indexed countN).participant
      (Fin cellsB) (Fin (CellLayout.Prime.cells remaining padsN)) Key where
  first := {
    view := fun _ => FingerprintRows.view (P.indexed countB).backend layout.binary
      (fun i => binaryLayout (.inl i)) (fun j => binaryLayout (.inr j))
    cutoff := cutoffB }
  second := {
    view := fun _ => FingerprintRows.view (R.indexed countN).backend layout.prime
      (fun i => primeLayout (.inl i)) (fun j => primeLayout (.inr j))
    cutoff := cutoffN }

theorem compile_selected_views (layout : Addresses P R cellsB remaining padsN)
    (countB countN cutoffB cutoffN : ℕ) {Key : Type}
    (coinsB : Coins B (Fin cellsB))
    (coinsN : Coins (ZMod p) (Fin (CellLayout.Prime.cells remaining padsN)))
    (targetB : B × B) (targetN : ZMod p × ZMod p)
    (result : StatementData A (P.indexed countB) (R.indexed countN))
    (h : compile P R A layout countB countN coinsB coinsN targetB targetN = some result)
    (key : Key) :
    (selected P R layout countB countN cutoffB cutoffN A.binaryLayout A.primeLayout).first.view key =
      FingerprintRows.view (P.indexed countB).backend result.primaryB
        (fun i => A.binaryLayout (.inl i)) (fun j => A.binaryLayout (.inr j)) ∧
    (selected P R layout countB countN cutoffB cutoffN A.binaryLayout A.primeLayout).second.view key =
      FingerprintRows.view (R.indexed countN).backend result.primaryN
        (fun i => A.primeLayout (.inl i)) (fun j => A.primeLayout (.inr j)) := by
  have hf := compile_fields P R A layout countB countN coinsB coinsN targetB targetN result h
  rw [hf.1, hf.2.1]
  exact ⟨rfl, rfl⟩

end StatementCompiler
end LfzkV2.Current
