import LfzkV2.Current.ZeroKnowledge.BackendRuntimeMixed

/-! Averaging fixes the base transcript table and full opening answer
before changing the independent prover coins. The resulting programmed
oracle remains part of the actual observer view. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeMixed
open ZeroKnowledge

#check @BackendRuntimeMixed.realAt_apply
#check @BackendRuntimeMixed.simulateAt_apply
#check @BackendRuntimeMixed.real_pair
#check @BackendRuntimeMixed.simulate_pair
#check @BackendRuntimeMixed.statClose
#print axioms BackendRuntimeMixed.realAt_apply
#print axioms BackendRuntimeMixed.simulateAt_apply
#print axioms BackendRuntimeMixed.statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeMixed
