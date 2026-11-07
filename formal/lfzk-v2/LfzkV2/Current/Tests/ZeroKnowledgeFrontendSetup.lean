import LfzkV2.Current.ZeroKnowledge.CompleteFrontendSetup
import LfzkV2.Current.ZeroKnowledge.FrontendCompletePayload

/-! Shared operational constructors are usable without either complete
simulator acceptance or whole-frontend distribution laws. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeFrontendSetup
open ZeroKnowledge

#check @CompleteSimulator.samples
#check @CompleteSimulator.base
#check @Frontend.CompleteCoupling.binaryMessageEquiv
#print axioms CompleteSimulator.samples
#print axioms CompleteSimulator.base
#print axioms Frontend.CompleteCoupling.binaryMessageEquiv
#print axioms Frontend.CompleteCoupling.binaryMessageEquiv_actual

end LfzkV2.Current.Tests.ZeroKnowledgeFrontendSetup
