import LfzkV2.Current.ZeroKnowledge.OracleBytes

/-! Canonical physical-byte recovery and freshness-counting axiom audit.
The physical input, not a caller-supplied parsed cache, owns H and all prior
query inputs.  No typed-query restriction is imposed on an observer. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleBytes

open ZeroKnowledge.OracleBytes

#print axioms decode_bytes
#print axioms canonical_bytes_injective
#print axioms replay_canonical
#print axioms decode_opening
#print axioms opening_root
#print axioms opening_responses
#print axioms opening_tagged_binary
#print axioms opening_tagged_prime
#print axioms opening_ancestor
#print axioms malformed_ne_opening
#print axioms raw_hit_card
#print axioms raw_hit_probability

end LfzkV2.Current.Tests.ZeroKnowledgeOracleBytes
