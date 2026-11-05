import LfzkV2.Layered.CausalReplay
import LfzkV2.Layered.PayloadReplay
import LfzkV2.HashReplay

/-!
# Prefix-only V2 tests at concrete message-prefix hash points

A point carries the commitment key, its block index, and just the messages
through that block. The test fills later messages and answers with defaults;
the causal replay theorem proves that those defaults cannot change it.
An inactive point with the same key handles out-of-range indices and the
zero-block circuit without adding a challenge or a root budget.
-/

namespace LfzkV2.Layered.Replay

open SumcheckV2 Linear.Challenges Bcs.TotalOracle

variable {F Pad C Key : Type} [Field F]

open LfzkV2.Replay (fillAnswers)

def fillMessages {n : ℕ} (pref : Fin n → Message F) : ℕ → Message F :=
  fun j => if h : j < n then pref ⟨j,h⟩ else .empty

noncomputable def prefixData (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (i : Fin (slots circuit)) (messages : Fin (i.val+1) → Message F) (pref : Fin i.val → C)
    (w : Cube input → F) (pads : Pad → F) : Data F (roleKind circuit ((roleEquiv circuit).symm i)) :=
  semanticData decode nonzero circuit plan (parsePayload circuit (fillMessages messages))
    (fillAnswers dflt pref) w pads ((roleEquiv circuit).symm i)

theorem prefixData_valid (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (i : Fin (slots circuit)) (messages : Fin (i.val+1) → Message F) (pref : Fin i.val → C)
    (w : Cube input → F) (pads : Pad → F) :
    Data.Valid (prefixData decode nonzero dflt circuit plan i messages pref w pads) :=
  semanticData_valid _ _ _ _ _ _ _ _ _

/-- Replaying a real prefix gives exactly the original algebraic test. -/
theorem prefixData_eq (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (payload : Payload circuit) (answers : ℕ → C) (i : Fin (slots circuit))
    (w : Cube input → F) (pads : Pad → F) :
    prefixData decode nonzero dflt circuit plan i (fun j => messageStream circuit payload j.val)
        (fun j => answers j.val) w pads =
      semanticData decode nonzero circuit plan payload answers w pads ((roleEquiv circuit).symm i) := by
  apply semanticData_eq_of_prefix
  · intro j hj
    have he : (roleEquiv circuit ((roleEquiv circuit).symm i)).val = i.val :=
      congrArg Fin.val ((roleEquiv circuit).apply_symm_apply i)
    exact dif_pos (he ▸ hj)
  · intro earlier he
    apply message_parse_eq
    intro prev hp
    have hi : (roleEquiv circuit prev).val < i.val+1 := by
      have hev := congrArg Fin.val ((roleEquiv circuit).apply_symm_apply i)
      omega
    rw [fillMessages,dif_pos hi]
    exact messageStream_at_role circuit payload prev

abbrev Point (Key F : Type) {out input : ℕ} (circuit : Layered.Circuit F out input) :=
  Key × Option ((i : Fin (slots circuit)) × (Fin (i.val+1) → Message F))

def pointAt {out input : ℕ} (circuit : Layered.Circuit F out input) (key : Key) (payload : Payload circuit)
    (i : Fin (slots circuit)) : Point Key F circuit :=
  (key,some ⟨i,fun j => messageStream circuit payload j.val⟩)

def hashInput {out input : ℕ} (circuit : Layered.Circuit F out input) (key : Key) (payload : Payload circuit)
    (i : ℕ) : Point Key F circuit :=
  if h : i < slots circuit then pointAt circuit key payload ⟨i,h⟩ else (key,none)

def points {out input : ℕ} (circuit : Layered.Circuit F out input) : PrefixPoints (Point Key F circuit) where
  slot point := match point.2 with | none => 0 | some p => p.1.val
  anc point j := match point.2 with
    | none => point
    | some p => let earlier := Transcript.ancestor (point.1,p) j
      (earlier.1,some earlier.2)
  anc_ne point j hj := by
    rcases point with ⟨key,opt⟩
    cases opt with
    | none =>
      change j < 0 at hj
      omega
    | some p =>
      intro heq
      apply Transcript.ancestor_ne (key,p) j hj
      have hkey : (Transcript.ancestor (key,p) j).1 = key :=
        congrArg (fun q : Point Key F circuit => q.1) heq
      have hbody : (Transcript.ancestor (key,p) j).2 = p :=
        Option.some.inj (congrArg (fun q : Point Key F circuit => q.2) heq)
      exact Prod.ext hkey hbody

omit [Field F] in
theorem hashInput_key {out input : ℕ} (circuit : Layered.Circuit F out input) (key : Key)
    (payload : Payload circuit) (i : ℕ) : (hashInput circuit key payload i).1 = key := by
  unfold hashInput
  split <;> rfl

omit [Field F] in
theorem hashInput_at {out input : ℕ} (circuit : Layered.Circuit F out input) (key : Key)
    (payload : Payload circuit) (i : Fin (slots circuit)) :
    hashInput circuit key payload i.val = pointAt circuit key payload i := by
  rw [hashInput,dif_pos i.isLt]

omit [Field F] in
theorem ancestor_at {out input : ℕ} (circuit : Layered.Circuit F out input) (key : Key)
    (payload : Payload circuit) (i : Fin (slots circuit)) (j : Fin i.val) :
    (points circuit).anc (pointAt circuit key payload i) j.val =
      pointAt circuit key payload ⟨j.val,j.isLt.trans i.isLt⟩ := by
  have h := Transcript.ancestor_at key (messageStream circuit payload) i j
  exact congrArg (fun p : Transcript.Point Key (Message F) (slots circuit) => (p.1,some p.2)) h

omit [Field F] in
theorem prefix_answers {out input : ℕ} (circuit : Layered.Circuit F out input)
    (H : Point Key F circuit → C) (key : Key) (payload : Payload circuit) (i : Fin (slots circuit)) :
    (points circuit).chal H (pointAt circuit key payload i) =
      fun j : Fin i.val => H (hashInput circuit key payload j.val) := by
  funext j
  rw [PrefixPoints.chal,ancestor_at,hashInput_at circuit key payload ⟨j.val,j.isLt.trans i.isLt⟩]

def pointKind {out input : ℕ} (circuit : Layered.Circuit F out input) (point : Point Key F circuit) : Kind :=
  match point.2 with
  | none => .ordinary (.output 0)
  | some p => roleKind circuit ((roleEquiv circuit).symm p.1)

noncomputable def pointData (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (point : Point Key F circuit) : (Fin ((points circuit).slot point) → C) →
      (Cube input → F) → (Pad → F) → Data F (pointKind circuit point) :=
  match point with
  | (_,none) => fun _ _ _ => (fun _ => 0)
  | (_,some ⟨i,messages⟩) => fun pref w pads => prefixData decode nonzero dflt circuit plan i messages pref w pads

theorem pointData_valid (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (point : Point Key F circuit) (pref : Fin ((points circuit).slot point) → C)
    (w : Cube input → F) (pads : Pad → F) :
    Data.Valid (pointData decode nonzero dflt circuit plan point pref w pads) := by
  rcases point with ⟨key,opt⟩
  cases opt with
  | none => trivial
  | some p => exact prefixData_valid _ _ _ _ _ p.1 p.2 _ _ _

/-- The counted point contains precisely the data used by the full verifier,
including every prior block answer recomputed at its own prefix point. -/
theorem pointData_eq (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F) (dflt : C)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (plan : PadPlan (Pad := Pad) circuit)
    (H : Point Key F circuit → C) (key : Key) (payload : Payload circuit) (i : Fin (slots circuit))
    (w : Cube input → F) (pads : Pad → F) :
    pointData decode nonzero dflt circuit plan (pointAt circuit key payload i)
        ((points circuit).chal H (pointAt circuit key payload i)) w pads =
      semanticData decode nonzero circuit plan payload (fun j => H (hashInput circuit key payload j))
        w pads ((roleEquiv circuit).symm i) := by
  change prefixData decode nonzero dflt circuit plan i _ _ w pads = _
  rw [prefix_answers]
  convert! prefixData_eq decode nonzero dflt circuit plan payload
    (fun j => H (hashInput circuit key payload j)) i w pads using 1

end LfzkV2.Layered.Replay
