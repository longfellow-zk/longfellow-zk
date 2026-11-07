import LfzkV2.Current.ZeroKnowledge.CompleteSimulatorLaw
import LfzkV2.Current.ZeroKnowledge.CompleteSimulatorVerifier
import LfzkV2.Current.ZeroKnowledge.CompleteResponse
import LfzkV2.Current.ZeroKnowledge.CompletePublicBody

/-! The simulator's public signature, pure honest response callback,
ordered public opening encoder, and exact full-observer frontend hybrid. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeCompleteSimulator
open ZeroKnowledge

#check @CompleteSimulator.simulate
#check @CompleteResponse.respond
#print axioms CompleteSimulator.simulate_accepts
#print axioms CompleteSimulator.frontend_sameDistribution
#print axioms CompleteSimulator.frontend_experiment_sameDistribution
#print axioms CompleteResponse.realResponses_eq
#print axioms CompleteResponse.respond_parsed
#print axioms CompletePublicBody.raw_honest
#print axioms CompletePublicBody.fill_raw_honest

end LfzkV2.Current.Tests.ZeroKnowledgeCompleteSimulator
