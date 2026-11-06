import LfzkV2.Current.FrontendVerifier
import LfzkV2.Current.FrontendTranscript
import Mathlib.Data.ZMod.Basic

namespace LfzkV2.Current.Tests.FrontendVerifier
open SumcheckV2
private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private def outputEntry : Layered.Entry (Cube 0) (Cube 0) 1 where
  carry _ := none
  fresh _ := ()

private def inputEntry : Layered.Entry (Cube 1) (Cube 1) 1 where
  carry := some
  fresh _ := (false, ())

private def body : LfzkV2.Native.CircuitLayer (Cube 0) (Cube 1) (Fin 0) (ZMod 101) where
  quadratic _ _ _ := 0
  linear _ _ := 1
  constant _ := 0
  assertions := Fin.elim0

private def circuit : Layered.Circuit (ZMod 101) 0 1 :=
  .entry 1 outputEntry (.layer 0 body (.entry 1 inputEntry .input))

private def payload : Layered.Replay.Payload circuit :=
  (⟨fun _ => ⟨3, 5⟩, 7, 11, 13⟩, ())

private def plan : Layered.Replay.PadPlan (Pad := Fin 6) circuit :=
  (⟨fun _ => (0, 1), 2, 3, 4, 5⟩, ())

-- One quadratic round and its three layer boundaries.  Both output and
-- input entries consume coefficients of existing answers.
example : FrontendReplay.slots circuit = 4 := rfl

example : FrontendTranscript.write circuit payload 0 = .empty := rfl
example : FrontendTranscript.write circuit payload 1 = .round ⟨3, 5⟩ := rfl
example : FrontendTranscript.write circuit payload 2 = .cross 7 := rfl
example : FrontendTranscript.write circuit payload 3 = .claims 11 13 := rfl

example : FrontendTranscript.read circuit (FrontendTranscript.write circuit payload) = payload :=
  FrontendTranscript.read_write circuit payload

-- A reader at the first quadratic round recovers its polynomial while
-- future cross/claim messages are absent.  They cannot leak through payload
-- reconstruction into that round's local test.
example :
    (FrontendTranscript.read circuit
      (FrontendTranscript.boundPrefix (FrontendTranscript.write circuit payload) 1)).1.rounds 0 =
      ⟨3, 5⟩ := rfl

example :
    (FrontendTranscript.read circuit
      (FrontendTranscript.boundPrefix (FrontendTranscript.write circuit payload) 1)).1.cross = 0 := rfl

-- The actual compiler-success proof is produced by reconstruction.  There
-- is no caller-supplied `built` field here.
example (answers : ℕ → ZMod 101) :
    Linear.buildConstraints
      (circuit.proof (FrontendReplay.read (fun a _ => a) (fun _ => ⟨1, one_ne_zero⟩)
        circuit plan payload answers) 0) =
      some (Current.FrontendVerifier.constraints circuit plan payload
        (fun a _ => a) (fun _ => ⟨1, one_ne_zero⟩) answers) :=
  Current.FrontendVerifier.constraints_built circuit plan payload
    (fun a _ => a) (fun _ => ⟨1, one_ne_zero⟩) answers

end LfzkV2.Current.Tests.FrontendVerifier
