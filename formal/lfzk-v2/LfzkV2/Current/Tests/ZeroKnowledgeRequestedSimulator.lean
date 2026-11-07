import LfzkV2.Current.ZeroKnowledge.RequestedSimulator
import LfzkV2.Current.ZeroKnowledge.CompleteObserver
import LfzkV2.Current.ZeroKnowledge.ObserverWindow

/-! Request values are installed by constructors; no public-value
correspondence assumption or finite raw-string universe is supplied. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeRequestedSimulator
open ZeroKnowledge

#check @RequestedSimulator.forRequest
#check @CompleteObserver.observe
#print axioms RequestedSimulator.requested_publics
#print axioms RequestedSimulator.requested_geometry
#print axioms RequestedSimulator.tapeEquiv
#print axioms ObserverWindow.before_output
#print axioms ObserverWindow.later_output

end LfzkV2.Current.Tests.ZeroKnowledgeRequestedSimulator
