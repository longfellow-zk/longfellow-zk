import polygero.Protocol.Instance

/-! Transmitted rows, openings, and exact expansion of optional masks. -/

namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def Instance.WireRow (I : Instance F) : Bool → Type
  | true => BatchedRow I.nw I.nq ⊕ Unit
  | false => CoreRow I.nw I.nq

instance (I : Instance F) (masks : Bool) : Fintype (I.WireRow masks) := by
  cases masks <;> unfold Instance.WireRow <;> infer_instance

omit [Fintype F] [DecidableEq F] in
theorem Instance.wireRow_card (I : Instance F) (masks : Bool) :
    Fintype.card (I.WireRow masks) = Fintype.card (CoreRow I.nw I.nq)+(if masks then 3 else 0) := by
  simp only [← Nat.card_eq_fintype_card]
  cases masks <;> simp only [WireRow, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Nat.card_sum, show Nat.card Unit = 1 from by simp,
    show Nat.card LinearConstraintMask = 2 from by rw [Nat.card_eq_fintype_card]; decide]

abbrev Instance.WireOracle (I : Instance F) (masks : Bool) := I.WireRow masks → Fin I.n → F

def Instance.expandWireOracle (I : Instance F) : (masks : Bool) → I.WireOracle masks → Oracle F I.nw I.nq I.n
  | true, W => ⟨⟨fun b i => W (.inl (.inl ⟨b,i⟩)), fun h => W (.inl (.inr h))⟩, W (.inr ())⟩
  | false, W => ⟨⟨fun b i => W ⟨b,i⟩, 0⟩, 0⟩

def Instance.compressWireOracle (I : Instance F) : (masks : Bool) → Oracle F I.nw I.nq I.n → I.WireOracle masks
  | true, W, .inl (.inl row) => W.ordinary.core row.1 row.2
  | true, W, .inl (.inr h) => W.ordinary.checkedMask h
  | true, W, .inr _ => W.proximityMask
  | false, W, row => W.ordinary.core row.1 row.2

omit [Fintype F] [DecidableEq F] in
theorem Instance.expand_compress (I : Instance F) (masks : Bool) (W : Oracle F I.nw I.nq I.n)
    (hz : masks = false → W.ordinary.checkedMask = 0 ∧ W.proximityMask = 0) :
    I.expandWireOracle masks (I.compressWireOracle masks W) = W := by
  cases masks with
  | true => cases W; rfl
  | false =>
    obtain ⟨hm,hp⟩ := hz rfl
    rcases W with ⟨⟨core,mask⟩,primary⟩
    change mask = 0 at hm
    change primary = 0 at hp
    subst mask; subst primary
    rfl

/-- Only the transmitted coordinates are needed to supply all verifier openings. -/
def Instance.wireOpening (I : Instance F) (masks : Bool) (Q : QuerySet I.n I.t)
    (values : I.WireRow masks → ↥Q.coordinates → F) : Opening F I.nw I.nq I.n I.t Q :=
  match masks with
  | true => (fun j => ⟨fun b i => values (.inl (.inl ⟨b,i⟩)) j,
      fun h => values (.inl (.inr h)) j⟩, fun j => values (.inr ()) j)
  | false => (fun j => ⟨fun b i => values ⟨b,i⟩ j, 0⟩, 0)

omit [Fintype F] [DecidableEq F] in
theorem Instance.wireOpening_eq (I : Instance F) (masks : Bool)
    (W : I.WireOracle masks) (Q : QuerySet I.n I.t) :
    I.wireOpening masks Q (fun i j => W i j.1) = openOracle (I.expandWireOracle masks W) Q := by
  cases masks <;> rfl

end RecursivePolygero
