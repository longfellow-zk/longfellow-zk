import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext

/-! The backend/frontend composition keeps private observer context and
its full history available to later queries. Only the selected canonical
request reaches protocol arithmetic. Validity is scoped to actual runs
under the same complementary SHA oracle. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContext
open ZeroKnowledge

#check @BackendRuntime.ContextTreeFamily
#check @BackendRuntime.observerContextForTrees
#check @BackendRuntimeContext.RequestReachable
#check @BackendRuntimeContext.simulator_statClose
#print axioms BackendRuntimeContext.before_reachable
#print axioms BackendRuntimeContext.backend_hiding
#print axioms BackendRuntimeContext.frontendCoupling_apply
#print axioms BackendRuntimeContext.frontendCoupling_view
#print axioms BackendRuntimeContext.simulator_statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContext
