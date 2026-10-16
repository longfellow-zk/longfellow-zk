import Lfzk.RbrZkFlatTape
import Lfzk.CompiledZk

/-! The terminal-pair split and the compiled verifier select the same built system. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.CompiledZk
open Lfzk.CompiledLongfellow (fieldLen_le)

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F]
  [Fintype F] [DecidableEq F] [SumcheckInterp F]
  [Fintype Gpt] [DecidableEq Gpt] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
variable {M ninp logw logc nl : ℕ} {w : ℕ → ℕ}
variable {V : ZkCode C F X Q Msg Gpt M ninp logw logc}
variable {H : ZkHonest F Lift logw logc}
variable {asg : Lift → LigeroAssignment ninp M F} {Sat : Lift → Prop}

/-- Complete a field prefix with arbitrary terminal answers.  The system
built before the Ligero challenge is independent of this completion. -/
def fillFieldPrefix [Inhabited C]
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) :
    Fin (Rounds.Role.length nl w) → C :=
  fun j => if h : j.val < Rounds.Role.layerBase w nl + 1
    then pref ⟨j.val, h⟩ else default

omit [Fintype C] in
theorem trunc_fillFieldPrefix [Inhabited C]
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) :
    Bcs.trunc (fillFieldPrefix (nl := nl) (w := w) pref)
      (Rounds.Role.layerBase w nl + 1) fieldLen_le = pref := by
  funext j
  simp [Bcs.trunc, fillFieldPrefix, j.isLt]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]
  [Inhabited Msg] in
/-- A compiled V1 statement is determined by the field prefix, even when
the prover queried either terminal hash input before transmitting it. -/
theorem zkBuilt_eq_of_fieldPrefix
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (tape tape' : Fin (Rounds.Role.length nl w) → C)
    (hprefix : Bcs.trunc tape (Rounds.Role.layerBase w nl + 1)
        fieldLen_le =
      Bcs.trunc tape' (Rounds.Role.layerBase w nl + 1)
        fieldLen_le) :
    zkBuilt (nl := nl) (w := w) V ms tape =
      zkBuilt (nl := nl) (w := w) V ms tape' := by
  unfold zkBuilt
  rw [hprefix]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [Fintype Q] [DecidableEq Q]
  [Inhabited Msg] in
/-- The built system selected from an arbitrary completion equals the one
used by the actual compiled verifier. -/
theorem zkBuilt_fillFieldPrefix_eq [Inhabited C]
    (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (ms : ℕ → Msg)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C)
    (hprefix : Bcs.trunc tape (Rounds.Role.layerBase w nl + 1)
      fieldLen_le = pref) :
    zkBuilt (nl := nl) (w := w) V ms
      (fillFieldPrefix (nl := nl) (w := w) pref) =
      zkBuilt (nl := nl) (w := w) V ms tape := by
  apply zkBuilt_eq_of_fieldPrefix V ms
  rw [trunc_fillFieldPrefix, hprefix]

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] [Inhabited Msg] in
/-- The compiled verifier builds exactly the system in the field-prefix
state of the extraction-first chain. -/
theorem built_state_eq_zkBuilt
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hprefix : Bcs.trunc tape (Rounds.Role.layerBase w nl + 1)
      fieldLen_le = pref)
    (sys : LigeroSystem ninp M F)
    (hs : (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms).state
      (Rounds.Role.layerBase w nl + 1) pref = .built sys) :
    zkBuilt (nl := nl) (w := w) V ms tape = some sys := by
  have hstate := state_eq_of
    (chain (nl := nl) (w := w) V H asg Sat (flatData LD) ms)
    (zkRun (nl := nl) (w := w) V ms
      (fun m pref => LD.accepting m pref (ms m)))
    rfl rfl (Rounds.Role.layerBase w nl + 1) pref
  have hacc := zk_state_acc_congr (nl := nl) (w := w) V ms
    (fun m pref => LD.accepting m pref (ms m))
    (fun _ _ _ _ => ∅) (Rounds.Role.layerBase w nl + 1)
    (by omega) pref
  unfold zkBuilt
  rw [hprefix]
  apply builtOf_eq_some.mpr
  rw [← hacc, ← hstate]
  exact hs

omit [Fintype C] [Fintype F] [DecidableEq F] [Fintype Gpt]
  [DecidableEq Gpt] [DecidableEq X] [DecidableEq Q] [Inhabited Msg] in
/-- The flat terminal branch identifies the same system used by `zkBuilt`.
This is the bridge from extraction-first LayerStep accounting to the
compiled V1 verifier. -/
theorem terminalPairAccept_zkBuilt
    (LD : ZkLigeroData C X Q Msg V asg) (ms : ℕ → Msg)
    (pref : Fin (Rounds.Role.layerBase w nl + 1) → C) (c d : C)
    (tape : Fin (Rounds.Role.length nl w) → C)
    (hprefix : Bcs.trunc tape (Rounds.Role.layerBase w nl + 1)
      fieldLen_le = pref)
    (hterm : terminalPairAccept (H := H) (Sat := Sat) LD ms pref c d) :
    ∃ sys : LigeroSystem ninp M F,
      zkBuilt (nl := nl) (w := w) V ms tape = some sys ∧
      Fits V sys ∧ NoSat asg sys ∧
      V.decodeQuery d ∈ LD.accepting
        (Rounds.Role.layerBase w nl + 2) (Bcs.extend pref c)
        (ms (Rounds.Role.layerBase w nl + 2)) sys (V.decodeChal c) := by
  obtain ⟨sys, hs, hf, hn, hq⟩ := hterm
  exact ⟨sys, built_state_eq_zkBuilt LD ms pref tape hprefix sys hs,
    hf, hn, hq⟩

end Lfzk.RbrZkFlat
