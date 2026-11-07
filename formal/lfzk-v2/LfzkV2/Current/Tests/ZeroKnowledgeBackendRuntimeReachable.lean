import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext

/-! Validity is scoped to actual earlier observer outputs under the same
complementary SHA oracle. A fixed request does not require witnesses for
unrelated public values. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeReachable
open ZeroKnowledge ApplicationSetup ConcreteSetup Frontend
open scoped Classical

#check @BackendRuntimeContext.RequestReachable
#check @BackendCompiled.simulator_statClose_on_runs
#check @BackendRuntimeContext.simulator_statClose
#print axioms BackendCompiled.cached_hiding_on_runs
#print axioms BackendCompiled.simulator_statClose_on_runs
#print axioms BackendRuntimeContext.before_reachable
#print axioms BackendRuntimeContext.frontendCoupling_view
#print axioms BackendRuntimeContext.simulator_statClose

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup) (outside : Bytes → Digest)

example (request : CanonicalRequest.Request shape binary.description.nPublic)
    (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) :
    BackendRuntimeContext.RequestReachable (C := C) (preM := 0) (preT := 0) binary prime primePlan repr shape setup
      id (Merkle.RandomOracle.TwoOracleTree.done request) outside request := ⟨outside,H,rfl⟩

example (chosen other : CanonicalRequest.Request shape binary.description.nPublic)
    (reachable : BackendRuntimeContext.RequestReachable (C := C) (preM := 0) (preT := 0) binary prime primePlan repr shape setup
      id (Merkle.RandomOracle.TwoOracleTree.done chosen) outside other) : other = chosen := by
  obtain ⟨_,_,same⟩ := reachable
  simpa only [Observer.run,id_eq] using same.symm

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeReachable
