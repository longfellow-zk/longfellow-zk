import LfzkV2.Current.ZeroKnowledge.FrontendSimulationHistory
import LfzkV2.Current.ZeroKnowledge.FrontendWriteLog
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalState
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationWrites
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalSimulation
import LfzkV2.Current.ZeroKnowledge.FrontendSetupAnswerTape
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationScalarAnswers
import LfzkV2.Current.ZeroKnowledge.FrontendStaticBody

/-! Audit the generated frontend's exact boundary sequence, stored writes,
and causal history before identifying it with the canonical verifier replay. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeFrontendPrefix

#print axioms ZeroKnowledge.Frontend.Prefix.execute_append
#print axioms ZeroKnowledge.Frontend.Prefix.circuit_state
#print axioms ZeroKnowledge.Frontend.WriteLog.execute_log
#print axioms ZeroKnowledge.Frontend.History.valid_replay
#print axioms ZeroKnowledge.Frontend.SimulationHistory.simulate_good
#print axioms ZeroKnowledge.Frontend.CanonicalState.matches_of_writes
#print axioms ZeroKnowledge.Frontend.CanonicalState.query_eq
#print axioms ZeroKnowledge.Frontend.SimulationWrites.binary_state
#print axioms ZeroKnowledge.Frontend.SimulationWrites.simulate_properties
#print axioms ZeroKnowledge.Frontend.BodyState.stored_writes
#print axioms ZeroKnowledge.Frontend.AnswerTape.query_lookup
#print axioms ZeroKnowledge.Frontend.AnswerTape.readSetup_initial_into
#print axioms ZeroKnowledge.Frontend.SimulationAnswers.first_future
#print axioms ZeroKnowledge.Frontend.SimulationScalarAnswers.first_values
#print axioms ZeroKnowledge.Frontend.CanonicalSimulation.batching_query
#print axioms ZeroKnowledge.Frontend.CanonicalSimulation.batching_tape
#print axioms ZeroKnowledge.Frontend.CanonicalSimulation.opening_query
#print axioms ZeroKnowledge.Frontend.StaticBody.oracle_irrel

end LfzkV2.Current.Tests.ZeroKnowledgeFrontendPrefix
