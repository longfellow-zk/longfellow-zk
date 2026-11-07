import LfzkV2.Current.ZeroKnowledge.BackendRuntimeSimulator

/-! The fixed-opening-answer hybrid ends at the actual witness-free
simulator, including the complete public parser and final seal. These
identities do not assume accepted-path or whole-view certificates. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeSimulator
open ZeroKnowledge

#check @BackendRuntimeSimulator.simulator_statClose
#print axioms CompleteObserverSimulation.complete_dummy
#print axioms BackendRuntimeEncoding.heap_value
#print axioms BackendRuntimeEncoding.heap_opening
#print axioms BackendRuntimeEncoding.runView_output
#print axioms BackendRuntimeEncoding.dummy_root
#print axioms BackendRuntimeSimulator.frontend_commitment
#print axioms BackendRuntimeSimulator.front_result
#print axioms BackendRuntimeSimulator.complete_requested
#print axioms BackendRuntimeSimulator.completed
#print axioms BackendRuntimeSimulator.simulatedPublic_eq
#print axioms BackendRuntimeSimulator.simulator_statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeSimulator
