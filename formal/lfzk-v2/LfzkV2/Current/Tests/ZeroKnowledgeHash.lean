import LfzkV2.Current.ZeroKnowledge.FrontendHash

/-! Removing the two adapter assertions preserves every wire value and
isolates precisely the trusted application checks. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeHash

#print axioms ZeroKnowledge.Frontend.Hash.above_eval_eq
#print axioms ZeroKnowledge.Frontend.Hash.above_satisfies_iff
#print axioms ZeroKnowledge.Frontend.Hash.build_satisfies_iff

end LfzkV2.Current.Tests.ZeroKnowledgeHash
