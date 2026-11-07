import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobalProof

/-! Actual complete honest/simulator endpoints share one fixed larger SHA
marginal. Private observer context and both mixed traces are retained; the
transcript oracle is the final independent factor. Validity is scoped to
actual same-SHA prior outputs rather than unrelated public requests. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextGlobal
open ZeroKnowledge

#check @BackendRuntimeGlobalCoins.PrivateProver
#check @BackendRuntimeGlobalCoins.PublicProver
#check @BackendRuntimeContextGlobal.statClose
#print axioms BackendRuntimeContextGlobal.restrict_oracle
#print axioms BackendRuntimeContextGlobal.backend_lift
#print axioms BackendRuntimeContextGlobal.simulator_global
#print axioms BackendRuntimeContextGlobal.hash_at_run
#print axioms BackendRuntimeContextGlobal.freshness
#print axioms BackendRuntimeContextGlobal.real_global
#print axioms BackendRuntimeContextGlobal.honest_global
#print axioms BackendRuntimeContextGlobal.opening_refresh
#print axioms BackendRuntimeContextGlobal.statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextGlobal
