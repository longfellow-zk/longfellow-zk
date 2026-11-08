import LfzkV2.Current.ZeroKnowledge.Error

namespace LfzkV2.Current.Tests.ZeroKnowledgeError

example : 0 ≤ ZeroKnowledge.Error.bound (2^320) (2^256) (2^128) 2443 84 0 0 0 :=
  ZeroKnowledge.Error.nonnegative _ _ _ _ _ _ _ _

example : merkleNonceBytes = 40 := rfl

example : Fintype.card MerkleNonce = 2^320 :=
  ZeroKnowledge.MerkleSimulation.nonce_card

example : 84*(merkleNonceBytes-32) = 672 := rfl

example : ZeroKnowledge.Error.bound (2^320) (2^256) (2^128) 2443 84 0 0 0 <
    1/(2:ℚ)^179 :=
  ZeroKnowledge.Error.rate7_at_query_budget 0 0 0 (by norm_num) (by norm_num)

#print axioms ZeroKnowledge.MerkleSimulation.nonce_card
#print axioms ZeroKnowledge.Error.rate7_at_query_budget
#print axioms ZeroKnowledge.Error.rate7_merkle
#print axioms ZeroKnowledge.Error.rate7
#print axioms ZeroKnowledge.Error.rate7_protocol

end LfzkV2.Current.Tests.ZeroKnowledgeError
