import LfzkV2.Current.ZeroKnowledge.SHAObserverWindow
import LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
import LfzkV2.Current.SHAOracle
import LfzkV2.Current.MdocIdentifiers

/-! The raw observer and internal identifier use the same SHA table. The
finite-window laws retain outside-domain calls in the actual mixed trace;
the probability law averages independent coordinates, not observed traces. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
open ZeroKnowledge

#check @SHAOracle.split
#check @SHAOracleProbability.conditional_statClose
#print axioms SHAOracle.observer_output
#print axioms SHAOracle.identifier_not_domain
#print axioms SHAOracle.fragment_identifier
#print axioms SHAObserverWindow.window_domain
#print axioms SHAOracleProbability.conditional_statClose

end LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
