import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling
import LfzkV2.Current.ZeroKnowledge.FrontendHonestStatement
import LfzkV2.Current.ZeroKnowledge.FrontendParserApplication
import LfzkV2.Current.ZeroKnowledge.FrontendRuntimeStatement
import LfzkV2.Current.ZeroKnowledge.FrontendCompilerTransport
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationMessages
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationParsed
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationSystem
import LfzkV2.Current.ZeroKnowledge.FrontendFullSatisfaction

/-! Audit the complete frontend, not just independently uniform message
marginals. The pointwise equality includes fingerprints, both circuits,
masked quotient advice, packing messages and the entire chained state. -/

#check LfzkV2.Current.ZeroKnowledge.Frontend.CompleteSimulation.simulate
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompleteHonest.binaryCandidate_project
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompleteHonest.primeCandidate_project
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompletePacking.fieldBits_inputs
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompletePacking.binaryPads_assignment
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompletePacking.packingInstance_valid
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling.generated_valid
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling.inner_view
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling.coupling_view
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullCoupling.sameDistribution
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.HonestAdapter.adapter_satisfies
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.HonestAdapter.generated_satisfies
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows.prime_rows_selected
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.HonestRows.binary_rows_selected
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.HonestStatement.rows
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.Parser.messages
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication.prime_success
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication.binary_success
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication.decode_success
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication.decode_requested
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.StatementShape.decoded_counts
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.StatementShape.decoded_rows
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.StatementShape.compile_success
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.RuntimeStatement.success
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.CompilerTransport.messages
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationMessages.prime_messages
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationMessages.binary_messages
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.PayloadTransport.same_body
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed.prime_frontend_rows
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed.prime_claim
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed.challenge_values
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed.binary_frontend_rows
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationSystem.initial_answer
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationSystem.decoded_rows
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.SimulationSystem.compiled_satisfies
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullSatisfaction.compiled_satisfies
#print axioms LfzkV2.Current.ZeroKnowledge.Frontend.FullSatisfaction.statement_exists
