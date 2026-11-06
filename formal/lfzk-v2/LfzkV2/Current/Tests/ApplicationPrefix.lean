import LfzkV2.Current.ApplicationPrefix
import Mathlib.Data.ZMod.Basic

namespace LfzkV2.Current.Tests.ApplicationPrefix
open SumcheckV2
open LfzkV2.Current.ApplicationPrefix

private def body : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 1) (Fin 0) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0
private def circuit : Layered.Circuit (ZMod 101) 0 1 := .layer 0 body .input
private def wire : ℕ → Option (Layered.Replay.Message (ZMod 101))
  | 1 => some (.round ⟨3,5⟩)
  | 2 => some (.cross 7)
  | 3 => some (.claims 11 13)
  | _ => some .empty

example : (Messages.read circuit wire).map (fun p =>
    ((p.1.rounds ⟨0,by decide⟩).c0,(p.1.rounds ⟨0,by decide⟩).c1,
      p.1.cross,p.1.claimA,p.1.claimB)) = some (3,5,7,11,13) := rfl
example : Messages.read circuit (fun q => if q = 1 then none else wire q) = none := rfl
example : Messages.read circuit (fun q => if q = 2 then some (.claims 7 0) else wire q) = none := rfl
example : Messages.read circuit (fun q => if q = 3 then none else wire q) = none := rfl

private def scalarBody : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 0) (Fin 0) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0
private def scalar : Layered.Circuit (ZMod 101) 0 0 := .layer 0 scalarBody .input
private def scalarWire : ℕ → Option (Layered.Replay.Message (ZMod 101))
  | 1 => some (.cross 7)
  | 2 => some (.claims 11 13)
  | _ => some .empty

-- A scalar layer still requires both terminal messages in the actual history.
example : (Messages.read scalar scalarWire).isSome = true := rfl
example : Messages.read scalar (fun q => if q = 1 then none else scalarWire q) = none := rfl
example : Messages.read scalar (fun q => if q = 2 then none else scalarWire q) = none := rfl

end LfzkV2.Current.Tests.ApplicationPrefix
