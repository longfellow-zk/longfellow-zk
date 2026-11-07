import LfzkV2.Current.ZeroKnowledge.BackendCompiled

/-! Compiled two-field backend axiom audit. The simulator's API takes public
frontend messages/rows and its own coins, with no honest logical-cell input. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendCompiled

open ZeroKnowledge.BackendCompiled

#check @ZeroKnowledge.BackendCompiled.simulate
#print axioms prepare_real
#print axioms prepare_sim
#print axioms cached_hiding
#print axioms simulator_statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendCompiled
