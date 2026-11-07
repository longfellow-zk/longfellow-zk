import LfzkV2.Current.ZeroKnowledge.OraclePrimaryFreshness

/-! Freshness is proved for the constructed canonical opening bytes, not
for a caller-supplied response identity. Malformed prior bytes remain in the
same prior-query set and are handled by the actual partial decoder. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOraclePrimaryFreshness
open ZeroKnowledge

example {B : Type} [Fintype B] (card : Fintype.card B = 2^128) :
    Fintype.card (Fin 361 → B) = 2^46208 := OraclePrimaryFreshness.gf128_mask_card card

#print axioms OracleResponse.block_before
#print axioms OracleResponse.batching_point
#print axioms OraclePrimaryFreshness.base_history
#print axioms OraclePrimaryFreshness.primary_formula
#print axioms OraclePrimaryFreshness.decoded_formula
#print axioms OraclePrimaryFreshness.raw_hit_probability

end LfzkV2.Current.Tests.ZeroKnowledgeOraclePrimaryFreshness
