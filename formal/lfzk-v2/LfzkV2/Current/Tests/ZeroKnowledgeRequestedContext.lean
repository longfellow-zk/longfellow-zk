import LfzkV2.Current.ZeroKnowledge.RequestedContextProbability
import LfzkV2.Current.ZeroKnowledge.RequestedContextSupport

/-! Actual requested prover/simulator endpoints with private observer
context retained through the complete raw pre/post view. The final support
corollary assumes no finite ambient private-state type. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeRequestedContext

#print axioms ZeroKnowledge.RequestedContextProjection.honest
#print axioms ZeroKnowledge.RequestedContextProjection.simulated
#print axioms ZeroKnowledge.RequestedContextProbability.window_statClose
#print axioms ZeroKnowledge.RequestedContextSupport.rawHonest
#print axioms ZeroKnowledge.RequestedContextSupport.rawSimulated
#print axioms ZeroKnowledge.RequestedContextSupport.statClose_raw_supported

end LfzkV2.Current.Tests.ZeroKnowledgeRequestedContext
