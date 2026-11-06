import LfzkV2.Current.ApplicationViewFrontend

namespace LfzkV2.Current.Tests.ApplicationViews
open SumcheckV2 LfzkV2.Current.ApplicationViews
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def layer : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 0) (ZMod 3) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0
private def circuit : Layered.Circuit (ZMod 3) 0 0 := .layer 0 layer .input
private def wire : ℕ → Option (Layered.Replay.Message (ZMod 3))
  | 1 => some (.cross 7)
  | 2 => some (.claims 11 13)
  | _ => none

-- The current cross term remains bound while future claims are unavailable.
example : (PartialMessages.read circuit wire 1).map (fun p =>
    (p.1.cross,p.1.claimA,p.1.claimB)) = some (7,0,0) := rfl

-- Malformed future data is not inspected before that round has begun.
example : (PartialMessages.read circuit (fun q => if q = 2 then some (.cross 23) else wire q) 1).isSome = true := rfl

-- Once a message is bound, absence or a wrong constructor rejects the view.
example : PartialMessages.read circuit (fun q => if q = 1 then none else wire q) 1 = none := rfl
example : PartialMessages.read circuit (fun q => if q = 2 then some (.cross 23) else wire q) 2 = none := rfl

example : (PartialMessages.read circuit wire 2).map (fun p =>
    (p.1.cross,p.1.claimA,p.1.claimB)) = some (7,11,13) := rfl

end LfzkV2.Current.Tests.ApplicationViews
