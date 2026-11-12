import LfzkV2.Current.ZeroKnowledge.FrontendBodyWrites

/-! The generated frontend's stored writes are exactly the complete body
prefix. Together with its causal history invariant, this identifies the
actual next query with the canonical batching query used by the verifier. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.BodyState

open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [DecidableEq B] in
theorem stored_writes (root : Digest) (context : Key) (coins : CompleteSimulation.Coins binary prime) :
    let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
    ∀ i, result.state.writes i = ProtocolWrites.fresh
      (CompleteFrontendBody.body binary prime primePlan root result)
      ⟨i.val,by have := i.isLt; have := result.state.rank.isLt; omega⟩ := by
  let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
  let body := CompleteFrontendBody.body binary prime primePlan root result
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H context coins
  have logs := properties.2.1.trans
    (BodyWrites.simulated_bodyPrefix binary prime primePlan samples base H root context coins)
  let desired := fun i : Fin result.state.rank.val => ProtocolWrites.fresh body
    ⟨i.val,by have := i.isLt; have := result.state.rank.isLt; omega⟩
  have reindex : List.ofFn desired = List.ofFn (fun i : Fin
      (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.val =>
      ProtocolWrites.fresh body
        ⟨i.val,i.isLt.trans (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.isLt⟩) := by
    simpa only [desired,Fin.val_cast] using List.ofFn_congr properties.1 desired
  have same : result.state.writes = desired := List.ofFn_injective (logs.trans reindex.symm)
  exact fun i => congrFun same i

omit [DecidableEq B] in
theorem pending_write (root : Digest) (context : Key) (coins : CompleteSimulation.Coins binary prime)
    (inside : (CompleteSimulation.simulate binary prime primePlan samples base H context coins).state.rank.val <
      (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length) :
    let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
    result.state.pending = ProtocolWrites.fresh (CompleteFrontendBody.body binary prime primePlan root result)
      ⟨result.state.rank.val,inside⟩ := by
  let result := CompleteSimulation.simulate binary prime primePlan samples base H context coins
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H context coins
  have index : (⟨result.state.rank.val,inside⟩ : Fin
      (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length) =
      (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex := Fin.ext properties.1
  dsimp only
  rw [index]
  exact properties.2.2.trans (BodyWrites.raw_pending binary prime primePlan root result.raw).symm

end LfzkV2.Current.ZeroKnowledge.Frontend.BodyState
