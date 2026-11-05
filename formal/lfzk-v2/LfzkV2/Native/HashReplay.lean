import LfzkV2.Native.CausalReplay
import LfzkV2.HashReplay

/-!
# Prefix-only V2 tests at concrete message-prefix hash points

A point carries the commitment key, its block index, and just the messages
through that block. The test fills later messages and answers with defaults;
the causal replay theorem proves that those defaults cannot change it.
An inactive point with the same key handles out-of-range indices and the
zero-block circuit without adding a challenge or a root budget.
-/

namespace LfzkV2.Native.Replay

open SumcheckV2 ChallengeBlocks Bcs.TotalOracle LfzkV2.Replay

variable {F Pad Slot C Key : Type} [Field F]

noncomputable def prefixData (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (i : Fin (slots circuit.shape)) (messages : Fin (i.val+1) → Message F) (pref : Fin i.val → C)
    (w : Cube input → F) (pads : Pad → F) : Data F (roleKind circuit.shape ((roleEquiv circuit.shape).symm i)) :=
  semanticData decode circuit plan (parsePayload circuit.shape (fillMessages messages))
    (fillAnswers dflt pref) w pads ((roleEquiv circuit.shape).symm i)

theorem prefixData_valid (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (i : Fin (slots circuit.shape)) (messages : Fin (i.val+1) → Message F) (pref : Fin i.val → C)
    (w : Cube input → F) (pads : Pad → F) :
    Data.Valid (prefixData decode dflt circuit plan i messages pref w pads) :=
  semanticData_valid _ _ _ _ _ _ _ _

/-- Replaying a real prefix gives exactly the original algebraic test. -/
theorem prefixData_eq (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (payload : Payload circuit) (answers : ℕ → C) (i : Fin (slots circuit.shape))
    (w : Cube input → F) (pads : Pad → F) :
    prefixData decode dflt circuit plan i (fun j => messageStream circuit.shape payload j.val)
        (fun j => answers j.val) w pads =
      semanticData decode circuit plan payload answers w pads ((roleEquiv circuit.shape).symm i) := by
  apply semanticData_eq_of_prefix
  · intro j hj
    have he : (roleEquiv circuit.shape ((roleEquiv circuit.shape).symm i)).val = i.val :=
      congrArg Fin.val ((roleEquiv circuit.shape).apply_symm_apply i)
    exact dif_pos (he ▸ hj)
  · intro earlier he
    apply message_parse_eq
    intro prev hp
    have hi : (roleEquiv circuit.shape prev).val < i.val+1 := by
      have hev := congrArg Fin.val ((roleEquiv circuit.shape).apply_symm_apply i)
      omega
    rw [fillMessages,dif_pos hi]
    exact messageStream_at_role circuit.shape payload prev

noncomputable def pointData (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (point : Point Key F circuit.shape) : (Fin ((points circuit.shape).slot point) → C) →
      (Cube input → F) → (Pad → F) → Data F (pointKind circuit.shape point) :=
  match point with
  | (_,none) => fun _ _ _ => (fun _ => 0)
  | (_,some ⟨i,messages⟩) => fun pref w pads => prefixData decode dflt circuit plan i messages pref w pads

theorem pointData_valid (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (point : Point Key F circuit.shape) (pref : Fin ((points circuit.shape).slot point) → C)
    (w : Cube input → F) (pads : Pad → F) :
    Data.Valid (pointData decode dflt circuit plan point pref w pads) := by
  rcases point with ⟨key,opt⟩
  cases opt with
  | none => trivial
  | some p => exact prefixData_valid _ _ _ _ p.1 p.2 _ _ _

/-- The counted point contains precisely the data used by the full verifier,
including every prior block answer recomputed at its own prefix point. -/
theorem pointData_eq (decode : (n : ℕ) → C → Fin n → F) (dflt : C)
    {out input : ℕ} (circuit : Circuit F out input) (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit)
    (H : Point Key F circuit.shape → C) (key : Key) (payload : Payload circuit) (i : Fin (slots circuit.shape))
    (w : Cube input → F) (pads : Pad → F) :
    pointData decode dflt circuit plan (pointAt circuit.shape key payload i)
        ((points circuit.shape).chal H (pointAt circuit.shape key payload i)) w pads =
      semanticData decode circuit plan payload (fun j => H (hashInput circuit.shape key payload j))
        w pads ((roleEquiv circuit.shape).symm i) := by
  change prefixData decode dflt circuit plan i _ _ w pads = _
  rw [prefix_answers]
  convert! prefixData_eq decode dflt circuit plan payload
    (fun j => H (hashInput circuit.shape key payload j)) i w pads using 1

end LfzkV2.Native.Replay
