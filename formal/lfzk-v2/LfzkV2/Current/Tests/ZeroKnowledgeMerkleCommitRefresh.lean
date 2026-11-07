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

example (H : Enc → Bool) :
    (ZeroKnowledge.MerkleRefresh.history (initial before) (input codec 2 nonce cells) (update 2) 3).run H =
      (actual codec 2 nonce cells before).run H := history_actual codec 2 nonce cells before H

example (H : Enc → Bool) :
    ((ZeroKnowledge.MerkleRefresh.history (initial before) (input codec 2 nonce cells) (update 2) 3).run H).1.2 1 =
      root (codec.withOracle H) 2 (nonce (before.run H).1) (cells (before.run H).1) :=
  history_root codec 2 nonce cells before (by decide) H

#print axioms finish_step
#print axioms history_request
#print axioms history_finish
#print axioms history_actual
#print axioms history_root

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitRefresh
