import LfzkV2.Current.FrontendBody
import Mathlib.Data.ZMod.Basic

namespace LfzkV2.Current.Tests.FrontendBody
open SumcheckV2

private def body : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 1) (Fin 0) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0

private def circuit : Layered.Circuit (ZMod 101) 0 1 := .layer 0 body .input
private def frontend : Frontend := ⟨[⟨[],[],1⟩],[]⟩
private def message : Current.LayerPayload (ZMod 101) 1 := ⟨fun _ => (3,5),7,(11,13)⟩
private def payload : Layered.Replay.Payload circuit := (⟨fun _ => ⟨3,5⟩,7,11,13⟩,())
private def frontendPayload : FrontendPayload (ZMod 101) frontend := fun i => by
  change Fin 1 at i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact message

example : FrontendBody.decode id circuit frontend frontendPayload = some payload := rfl
example : FrontendBody.read id circuit [] = none := rfl
example : FrontendBody.read id circuit [⟨2,⟨fun _ => (3,5),7,(11,13)⟩⟩] = none := rfl
example : FrontendBody.read id circuit [⟨1,message⟩,⟨1,message⟩] = none := rfl

example : FrontendBody.read id circuit (FrontendBody.write circuit payload) = some payload :=
  FrontendBody.read_write circuit payload

-- A scalar layer has no quadratic round polynomials, but still carries its
-- terminal cross coefficient and masked claims. It must not disappear.
private def scalarBody : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 0) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0
private def scalar : Layered.Circuit (ZMod 101) 0 0 := .layer 0 scalarBody .input

example : FrontendBody.read id scalar [] = none := rfl
example : (FrontendBody.read id scalar [⟨0,⟨Fin.elim0,7,(11,13)⟩⟩]).isSome = true := rfl

end LfzkV2.Current.Tests.FrontendBody
