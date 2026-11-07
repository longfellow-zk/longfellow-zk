import LfzkV2.Current.ZeroKnowledge.OracleRefresh

/-! The honest opening refresh uses a causal prefix tree. These interfaces
have no complete-proof/H-dependent pending-message certificate and no
Q-dependent simulator response in the input being refreshed. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleRefresh
open ZeroKnowledge

#print axioms OracleRefresh.one_step
#print axioms OracleRefresh.prefix_queries_before
#print axioms OracleRefresh.fresh_iff_prior
#print axioms OracleRefresh.prefix_preserved
#print axioms OracleRefresh.whole_answer
#print axioms OracleRefresh.refresh_sameDistribution

end LfzkV2.Current.Tests.ZeroKnowledgeOracleRefresh
