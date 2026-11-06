import LfzkV2.Current.FrontendSchedule
import Mathlib.Data.ZMod.Basic

namespace LfzkV2.Current.Tests.FrontendSchedule
open SumcheckV2 LfzkV2.Current.FrontendSchedule

private def entering : EntryMetadata 1 := ⟨[⟨7,1⟩],rfl⟩
private def inputs : EntryMetadata 1 := ⟨[⟨9,1⟩],rfl⟩
private def outputEntry : Layered.Entry (Cube 0) (Cube 0) 1 where
  carry _ := none
  fresh _ := ()
private def inputEntry : Layered.Entry (Cube 0) (Cube 0) 1 where
  carry _ := some ()
  fresh _ := ()

private def body : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 2) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 0
  constant _ := 0
  assertions i := if i.val = 0 then .quadratic () () else .linear ()

private def metadata : LayerMetadata body where
  fragments := [⟨7,0,1,1⟩]
  count := rfl
  quadratic_first i := by fin_cases i <;> rfl

private def circuit : Layered.Circuit (ZMod 101) 0 0 :=
  .entry 1 outputEntry (.layer 2 body (.entry 1 inputEntry .input))
private def plan : Plan (ZMod 101) circuit :=
  .entryLayer entering outputEntry metadata (.inputEntry inputs inputEntry)

-- Output coefficients and both marker classes share one assertion answer.
-- The final input coefficient shares alpha's answer after the claims.
example : FrontendReplay.slots circuit = 3 := rfl
example : plan.frontend.roles .binary =
    [.assertions .binary 0 entering.entries metadata.fragments,
      .terminal .binary 0,.combine .binary 0 inputs.entries] := rfl
example : plan.capacity = 3 := rfl
example : FrontendReplay.Coalesced circuit := plan.coalesced
example : FrontendReplay.Fits plan.capacity circuit 0 := plan.fits

private def inputRole : Layered.Replay.LayerRole circuit :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨0,by decide⟩)))))
example : FrontendReplay.queryIndex circuit inputRole 0 = 2 := rfl
example : plan.locatedRole .binary 0 inputRole = .combine .binary 0 inputs.entries := rfl
example : frontendSide (plan.locatedRole .binary 0 inputRole) = some .binary :=
  plan.locatedRole_side .binary 0 inputRole
example : (plan.locatedRole .binary 0 inputRole).domain = .combine := rfl
example : coordinates (plan.locatedRole .binary 0 inputRole) = 2 := rfl

-- A quadratic marker cannot be declared as part of an all-linear block.
example : ¬ (∀ i : Fin 2, isQuadratic (body.assertions i) = decide (i.val < 0)) := by
  intro h
  have hc := h 0
  contradiction

-- Even an input-only frontend with an empty coefficient vector retains
-- its one actual assertion boundary; it creates no proof payload layers.
private def inputPlan : Plan (ZMod 101) (.input (n := 0)) := .input
example : inputPlan.frontend.roles .prime = [.inputAssertions .prime []] := rfl
example : FrontendReplay.slots (.input (F := ZMod 101) (n := 0)) = 1 := rfl
example : inputPlan.capacity = 0 := rfl

end LfzkV2.Current.Tests.FrontendSchedule
