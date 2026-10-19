import polygero.Recursion.FSRootCommit

/-! A concrete injective typed encoding for both leaf roles and shared nodes.
Encoding contributes no probabilistic soundness term. -/
namespace RecursivePolygero.FiatShamir.MerkleFS
open Merkle.MH
variable {F D SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

abbrev Encoding := ((SaltP × Leaf I) ⊕ (SaltC × Leaf child.instance)) ⊕ (D × D)

def parentCodec : Codec SaltP (Leaf I) D (Encoding child (D := D) (SaltP := SaltP) (SaltC := SaltC)) where
  leafEnc sm := .inl (.inl sm)
  nodeEnc dd := .inr dd

def childCodec : Codec SaltC (Leaf child.instance) D (Encoding child (D := D) (SaltP := SaltP) (SaltC := SaltC)) where
  leafEnc sm := .inl (.inr sm)
  nodeEnc dd := .inr dd

def parentDecoders : RoleDecoders (parentCodec child (D := D) (SaltP := SaltP) (SaltC := SaltC)) where
  leafDec
    | .inl (.inl sm) => some sm
    | _ => none
  nodeDec
    | .inr dd => some dd
    | _ => none
  leaf_roundTrip _ := rfl
  node_roundTrip _ := rfl
  leaf_sound := by intro x sm h; rcases x with (a | b) | c <;> simp_all [parentCodec]
  node_sound := by intro x dd h; rcases x with (a | b) | c <;> simp_all [parentCodec]

def childDecoders : RoleDecoders (childCodec child (D := D) (SaltP := SaltP) (SaltC := SaltC)) where
  leafDec
    | .inl (.inr sm) => some sm
    | _ => none
  nodeDec
    | .inr dd => some dd
    | _ => none
  leaf_roundTrip _ := rfl
  node_roundTrip _ := rfl
  leaf_sound := by intro x sm h; rcases x with (a | b) | c <;> simp_all [childCodec]
  node_sound := by intro x dd h; rcases x with (a | b) | c <;> simp_all [childCodec]

end RecursivePolygero.FiatShamir.MerkleFS
