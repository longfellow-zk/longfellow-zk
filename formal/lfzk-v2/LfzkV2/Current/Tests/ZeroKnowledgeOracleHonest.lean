import LfzkV2.Current.ZeroKnowledge.OracleHonestFreshness
import LfzkV2.Current.ZeroKnowledge.OracleHonestCoins
import LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshBound

/-! Kernel assumption audit for the concrete honest opening refresh.
Each source-facing constructor uses the actual staged frontend/parser and
canonical encoder. The probability law retains aborts and the whole updated
oracle, so later repeated queries are part of the covered observation. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleHonest

#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical.batching_query
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical.opening_query
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.pending_output
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.input_output
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.internal_fresh
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.active_output
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.input_active
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.active_input_queries
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestTree.active_point_queries
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestCoins.equivalence
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability.probability_mono
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability.statClose_of_probability
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshProbability.statClose
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior.statClose_of_probability
#print axioms LfzkV2.Current.ZeroKnowledge.OracleRefreshPrior.statClose
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh.finish_next
#print axioms LfzkV2.Current.ZeroKnowledge.OracleHonestRefresh.statClose

end LfzkV2.Current.Tests.ZeroKnowledgeOracleHonest
