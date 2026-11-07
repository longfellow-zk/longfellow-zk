import LfzkV2.Current.ZeroKnowledge.BackendRuntime
import LfzkV2.Current.ZeroKnowledge.MerkleRuntimeTransport
import LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation

/-! Actual canonical proof encoding is part of the fixed-opening-answer
backend law; the only remaining algebraic interface here is ordinary truth
of the compiled affine rows, discharged at the frontend boundary. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntime
open ZeroKnowledge

#check @BackendRuntime.simulator_statClose
#print axioms BackendRuntime.backend_hiding
#print axioms BackendRuntime.front_equiv
#print axioms BackendRuntime.frontendCoupling_view
#print axioms BackendRuntime.simulator_statClose
#print axioms MerkleRuntimeTransport.commitLabels_eq
#print axioms MerkleRuntimeTransport.commitPass_run
#print axioms CompleteObserverSimulation.body_honest
#print axioms CompleteObserverSimulation.body_dummy
#print axioms CompleteObserverSimulation.statementAt_body

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntime
