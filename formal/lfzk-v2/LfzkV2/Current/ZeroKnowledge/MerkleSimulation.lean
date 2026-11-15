import Merkle.Commit

/-! A public column index can be included in a generic Merkle leaf message.
Only its nonce is random.  For hiding we therefore
regard the column index as part of the message, rather than silently treating
the pair `(index,nonce)` as uniform randomness.  This is a change of analysis
coordinates: every encoded byte, heap label and opening check is unchanged. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleSimulation

open Merkle Merkle.MH Finset
open scoped Classical

section Reindex
variable {Index Nonce Leaf D Enc : Type}
variable (codec : Codec (Index × Nonce) Leaf D Enc)

def shuffle : (Nonce × (Index × Leaf)) ≃ ((Index × Nonce) × Leaf) where
  toFun x := ((x.2.1,x.1),x.2.2)
  invFun x := (x.1.2,(x.1.1,x.2))
  left_inv _ := rfl
  right_inv _ := rfl

def nonceCodec : Codec Nonce (Index × Leaf) D Enc where
  leafEnc x := codec.leafEnc (shuffle x)
  nodeEnc := codec.nodeEnc

theorem nonceCodec_inj (injective : codec.Inj) : (nonceCodec codec).Inj :=
  ⟨injective.leaf.comp shuffle.injective,injective.node⟩

@[simp] theorem nonceCodec_leaf (index : Index) (nonce : Nonce) (leaf : Leaf) :
    (nonceCodec codec).leafEnc (nonce,(index,leaf)) = codec.leafEnc ((index,nonce),leaf) := rfl

@[simp] theorem nonceCodec_node (children : D × D) :
    (nonceCodec codec).nodeEnc children = codec.nodeEnc children := rfl

end Reindex

end LfzkV2.Current.ZeroKnowledge.MerkleSimulation
