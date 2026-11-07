import LfzkV2.Current.ZeroKnowledge.MerkleBound
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkle
open ZeroKnowledge.MerkleSimulation

-- The index is public message data. Reusing a nonce does not erase it.
example {Index Nonce Leaf D Enc : Type} (C : Merkle.MH.Codec (Index × Nonce) Leaf D Enc)
    (injective : C.Inj) (first second : Index) (different : first ≠ second)
    (nonce : Nonce) (leaf : Leaf) :
    (nonceCodec C).leafEnc (nonce,(first,leaf)) ≠
      (nonceCodec C).leafEnc (nonce,(second,leaf)) := by
  intro equal
  have h := (nonceCodec_inj C injective).leaf equal
  exact different (congrArg (fun x : Nonce × (Index × Leaf) => x.2.1) h)

example : Fintype.card Digest = 2^256 := digest_card

example (queries : ℕ) :
    openingError (2^256) (2^256) 2443 (2443-84) queries =
      (47731336+4718*(queries:ℚ))/(2:ℚ)^256 := rate7_openingError queries

#print axioms commit_labels
#print axioms check_values
#print axioms opening_hiding
#print axioms rate7_openingError

end LfzkV2.Current.Tests.ZeroKnowledgeMerkle
