import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody

/-! The public simulator samples every serialized frontend message from
its independent coins. Oracle answers determine the derived affine claims
and execution state, which are recomputed by the verifier and are absent
from this body. Normalizing unused oracle coordinates cannot change it. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.StaticBody
open ApplicationSetup ConcreteSetup
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (first second : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [DecidableEq B] in
theorem oracle_irrel (root : Digest) (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    CompleteFrontendBody.body binary prime primePlan root
        (CompleteSimulation.simulate binary prime primePlan samples base first context coins) =
      CompleteFrontendBody.body binary prime primePlan root
        (CompleteSimulation.simulate binary prime primePlan samples base second context coins) := rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.StaticBody
