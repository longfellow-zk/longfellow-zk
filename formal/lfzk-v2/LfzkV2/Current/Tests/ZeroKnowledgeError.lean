import LfzkV2.Current.ZeroKnowledge.Error

namespace LfzkV2.Current.Tests.ZeroKnowledgeError

example : 0 ≤ ZeroKnowledge.Error.bound (2^256) (2^256) (2^128) 2443 84 0 0 0 :=
  ZeroKnowledge.Error.nonnegative _ _ _ _ _ _ _ _

#print axioms ZeroKnowledge.Error.rate7_merkle
#print axioms ZeroKnowledge.Error.rate7
#print axioms ZeroKnowledge.Error.rate7_protocol

end LfzkV2.Current.Tests.ZeroKnowledgeError
