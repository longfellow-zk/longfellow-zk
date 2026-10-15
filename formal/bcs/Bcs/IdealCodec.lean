import Merkle.Extraction

/-!
# The ideal role encoding

`Merkle`'s theorems are parametric in the encoding type `Enc` and ask only for same-role
injectivity (`Codec.Inj`) or, for extraction, executable partial inverses (`RoleDecoders`).  Taking

```
Enc := (Salt × M) ⊕ (D × D)
```

supplies both for *any* message type, with `rfl` proofs.  That is what keeps serialization off the
critical path: the compiler and its soundness theorem can be proved at this codec, and the concrete
byte encoding (`Merkle.MH.concreteCodec`) swapped in afterwards, at the parameter point, without
restating anything.

The one thing given up is range overlap: the sum type is domain-separated, which is a *stronger*
hypothesis than merkle's theorems need (`concrete_ranges_overlap_iff` shows the deployed 32-byte
instance really does overlap).  So a concrete instantiation still owes `RoleDecoders` for
`concreteCodec`; it is not owed by anything proved against `idealCodec`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs

open Merkle

/-- The two role serializations as the two injections of a sum. -/
abbrev IdealEnc (Salt M D : Type*) := (Salt × M) ⊕ (D × D)

/-- The ideal codec: leaves left, nodes right. -/
def idealCodec (Salt M D : Type*) : MH.Codec Salt M D (IdealEnc Salt M D) where
  leafEnc := Sum.inl
  nodeEnc := Sum.inr

@[simp] theorem idealCodec_leafEnc (Salt M D : Type*) (sm : Salt × M) :
    (idealCodec Salt M D).leafEnc sm = Sum.inl sm := rfl

@[simp] theorem idealCodec_nodeEnc (Salt M D : Type*) (dd : D × D) :
    (idealCodec Salt M D).nodeEnc dd = Sum.inr dd := rfl

/-- Its decoders: the two projections.  Every law is `rfl` or a case split. -/
def idealDecoders (Salt M D : Type*) : MH.RoleDecoders (idealCodec Salt M D) where
  leafDec x := x.elim some fun _ ↦ none
  nodeDec x := x.elim (fun _ ↦ none) some
  leaf_roundTrip _ := rfl
  node_roundTrip _ := rfl
  leaf_sound x sm h := by cases x <;> simp_all
  node_sound x dd h := by cases x <;> simp_all

/-- Same-role injectivity, for free. -/
theorem idealCodec_inj (Salt M D : Type*) : (idealCodec Salt M D).Inj :=
  (idealDecoders Salt M D).inj

end Bcs
