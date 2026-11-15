import LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh

/-! A prior query can coincide with a commitment query. The deterministic
correspondence still preserves its repeated answer and the entire trace;
freshness belongs to a separate probability bound. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitRefresh

open Merkle Merkle.MH Merkle.RandomOracle ZeroKnowledge.MerkleCommitRefresh

abbrev Enc := (Bool × Bool) ⊕ (Bool × Bool)

def codec : Codec Bool Bool Bool Enc where
  leafEnc := Sum.inl
  nodeEnc := Sum.inr

def before : Tree Enc Bool Bool 1 :=
  .query (.inr (false,false)) fun answer => .done answer

def nonce (_request : Bool) (_column : Fin 2) : Bool := false
def cells (request : Bool) (_column : Fin 2) : Bool := request

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitRefresh
