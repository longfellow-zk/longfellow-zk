import LfzkV2.Current.FrontendReplay
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Field.ZMod

namespace LfzkV2.Current.Tests.FrontendReplay
open SumcheckV2
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private def entry (carry : Bool) : Layered.Entry (Cube 0) (Cube 0) 1 where
  carry _ := if carry then some () else none
  fresh _ := ()

private def body : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 1) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions _ := .linear ()

private def circuit : Layered.Circuit (ZMod 101) 0 0 :=
  .entry 1 (entry false) (.layer 1 body (.entry 1 (entry true) .input))

private def plan : Layered.Replay.PadPlan (Pad := Unit) circuit :=
  (⟨Fin.elim0, (), (), (), ()⟩, ())

private def payload : Layered.Replay.Payload circuit :=
  (⟨Fin.elim0, 0, 0, 0⟩, ())

private def messages : Layered.Circuit.Messages Unit circuit :=
  Current.FrontendReplay.read (fun (a : ZMod 101) (i : ℕ) => a*10+(i : ZMod 101))
    (fun _ => ⟨1, one_ne_zero⟩) circuit plan payload (fun n => (n : ZMod 101)+5)

-- One scalar layer has three boundaries despite both entry blocks.
example : Current.FrontendReplay.slots circuit = 3 := rfl

-- Entry and explicit assertion coefficients extend the same first answer.
example : messages.1 0 = 50 ∧ messages.2.1.beta 0 = 51 := by
  dsimp [messages, Current.FrontendReplay.read, circuit, plan, payload,
    Current.FrontendReplay.readFrom]
  norm_num

-- The input entry extends the last combine answer after alpha, without
-- another query. Distinct tens distinguish query changes from cursor changes.
example : messages.2.1.alpha = 70 ∧ messages.2.2.1 0 = 71 := by
  dsimp [messages, Current.FrontendReplay.read, circuit, plan, payload,
    Current.FrontendReplay.readFrom, Current.FrontendReplay.hasLayers]
  norm_num

end LfzkV2.Current.Tests.FrontendReplay
