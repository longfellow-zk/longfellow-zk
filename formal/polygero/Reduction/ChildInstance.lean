import polygero.Protocol.Instance
import polygero.Reduction.Link
import polygero.Reduction.CoefficientStatement

/-! Child encoding, coefficient substitution, and exact witness reconstruction. -/

namespace RecursivePolygero
open Finset Polynomial Codes LigeroFamily RecursivePolygero.Local RecursivePolygero.Local.Polygero
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- All child encoding parameters are fixed before execution. The child equation
index type depends only on the parent query count. -/
structure Child (I : Instance F) where
  r : ℕ
  w : ℕ
  n : ℕ
  d : ℕ
  slots : ℕ
  s : ℕ
  t : ℕ
  domain : ReedSolomon.Domain F r w n
  layout : ConstraintLayout F slots w
  primary_le : r+w+s ≤ n
  query_le : t ≤ n
  packing : Packing (I.r+I.w) I.s d slots

noncomputable def Child.instance {I : Instance F} (C : Child I) : Instance F where
  q := C.slots
  r := C.r
  w := C.w
  n := C.n
  nw := C.d
  nq := 0
  s := C.s
  t := C.t
  Equations := InnerEquations I.t
  equationsFinite := Fintype.ofFinite _
  equationsDecidable := Classical.decEq _
  domain := C.domain
  layout := C.layout
  primary_le := C.primary_le
  query_le := C.query_le

noncomputable def Child.link {I : Instance F} (C : Child I) : Link I.layer C.instance.layer where
  decode witness := unpack C.packing (flatten witness)
  statement σ W c Q := coefficientStatement I.domain (by have := I.primary_le; omega)
    I.layout σ C.packing c Q (openOracle W Q)
  direct W Q := directProducts Q (openOracle W Q)
  sound σ W c Q witness hd hs :=
    ((verifier_factorization I.domain (by have := I.primary_le; omega) I.layout σ C.packing c Q
      (openOracle W Q) witness).mp ⟨hd,hs⟩)

/-- Exact substitution holds for each fixed child witness, in both directions. -/
theorem Child.verify_iff {I : Instance F} (C : Child I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (coin : I.layer.Coin)
    (Q : I.layer.Query) (witness : C.instance.layer.Witness) :
    C.link.direct W Q ∧ C.instance.layer.satisfies (C.link.statement σ W coin Q) witness ↔
      I.layer.verify σ W coin (C.link.decode witness) Q :=
  verifier_factorization I.domain (by have := I.primary_le; omega) I.layout σ C.packing coin Q
    (openOracle W Q) witness

end RecursivePolygero
