import LfzkV2.Current.HashCircuit

/-! Removing the two adapter assertions preserves every wire value and
isolates precisely the trusted application checks. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeHash

#print axioms HashCircuit.above_eval_eq
#print axioms HashCircuit.above_satisfies_iff
#print axioms HashCircuit.build_satisfies_iff

end LfzkV2.Current.Tests.ZeroKnowledgeHash
