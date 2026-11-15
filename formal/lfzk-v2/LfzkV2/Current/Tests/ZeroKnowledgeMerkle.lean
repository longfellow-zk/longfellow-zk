import LfzkV2.Current.ZeroKnowledge.MerkleSimulation
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

end LfzkV2.Current.Tests.ZeroKnowledgeMerkle
