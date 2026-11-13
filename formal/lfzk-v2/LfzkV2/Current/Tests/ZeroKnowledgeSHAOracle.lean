import LfzkV2.Current.ZeroKnowledge.SHAObserverWindow
import LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
import LfzkV2.Current.SHASetupDomains

/-! The raw observer and internal identifier use the same SHA table. The
finite-window laws retain outside-domain calls in the actual mixed trace;
the probability law averages independent coordinates, not observed traces. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
open ZeroKnowledge

#check @SHAOracle.split
#check @SHAOracleProbability.conditional_statClose
#check @SHAObserverWindow.before_output
#check @SHAObserverWindow.later_output
#print axioms SHAOracle.observer_output
#print axioms SHAOracle.identifier_not_domain
#print axioms SHAOracle.fragment_identifier
#print axioms SHAOracle.context_hash
#print axioms SHAOracle.joint_context_hash
#print axioms SHAObserverWindow.window_domain
#print axioms SHAObserverWindow.before_output
#print axioms SHAObserverWindow.later_output
#print axioms SHAOracleProbability.split_sameDistribution
#print axioms SHAOracleProbability.conditional_statClose

end LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
