import LfzkV2.Layered.Joint.Side
import LfzkV2.Transcript

/-!
# The mdoc joint transcript

Both frontends, including the binary packing response, precede every backend
challenge. The first backend point fixes the ordered pair of statements. The
last point fixes both typed responses and draws the one shared column query.
Per-field backend schedules are used only to reuse local algebraic proofs;
the actual transcript below has a single opening role.
-/

namespace LfzkV2.Layered.Joint.Replay

open RecursivePolygero Bcs.TotalOracle
open LfzkV2.Joint (Participant Family)
open scoped Classical

variable {F₁ F₂ Key C Public : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Layered.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Layered.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}

abbrev Context (Key C Public : Type) := Key × C × Public

variable (S₁ : Layered.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Layered.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)

abbrev Frontends := Side.Frontend S₂
abbrev Proof := Frontends S₁ S₂ × I₁.layer.Payload × I₂.layer.Payload

def firstFrontend (proof : Proof S₁ S₂) : Side.Frontend S₁ := proof.1.1.1
def context (proof : Proof S₁ S₂) : Context Key C Public := (firstFrontend S₁ S₂ proof).1.1
def selectedOne (proof : Proof S₁ S₂) : S₁.Selected := (firstFrontend S₁ S₂ proof, proof.2.1)
def selectedTwo (proof : Proof S₁ S₂) : S₂.Selected := (proof.1, proof.2.2)

def secondStart : ℕ := 1 + Side.steps S₁
def backendStart : ℕ := secondStart S₁ + Side.steps S₂
def slots : ℕ := backendStart S₁ S₂ + 3

/-- Frontend messages carry exactly the existing causal field point. The
statement payload contains no backend response; only the query message does. -/
inductive Message where
  | empty
  | first (point : S₁.Domain)
  | second (point : S₂.Domain)
  | statements (frontends : Frontends S₁ S₂)
  | responses (first : I₁.layer.Payload) (second : I₂.layer.Payload)

private def Message.equiv : Message S₁ S₂ ≃
    Unit ⊕ S₁.Domain ⊕ S₂.Domain ⊕ Frontends S₁ S₂ ⊕ (I₁.layer.Payload × I₂.layer.Payload) where
  toFun
    | .empty => .inl ()
    | .first p => .inr (.inl p)
    | .second p => .inr (.inr (.inl p))
    | .statements p => .inr (.inr (.inr (.inl p)))
    | .responses p q => .inr (.inr (.inr (.inr (p,q))))
  invFun
    | .inl _ => .empty
    | .inr (.inl p) => .first p
    | .inr (.inr (.inl p)) => .second p
    | .inr (.inr (.inr (.inl p))) => .statements p
    | .inr (.inr (.inr (.inr (p,q)))) => .responses p q
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with u | p | p | p | ⟨p,q⟩
    · cases u; rfl
    all_goals rfl

noncomputable instance messageFintype [Fintype Key] [Fintype Public]
    [Fintype S₁.Data] [Fintype S₂.Data] : Fintype (Message S₁ S₂) := by
  letI : Fintype (Side.Frontend S₁) := inferInstanceAs (Fintype (((Key × C × Public) × S₁.Data) × F₁))
  letI : Fintype S₁.Domain := inferInstance
  letI : Fintype S₂.Domain := inferInstance
  letI : Fintype (Frontends S₁ S₂) := inferInstance
  exact Fintype.ofEquiv _ (Message.equiv S₁ S₂).symm

abbrev Domain := Transcript.Point Key (Message S₁ S₂) (slots S₁ S₂)

def messages (proof : Proof S₁ S₂) (j : ℕ) : Message S₁ S₂ :=
  if j = 0 then .empty
  else if j < secondStart S₁ then .first (S₁.hashInput (selectedOne S₁ S₂ proof) (j-1))
  else if j < backendStart S₁ S₂ then .second (S₂.hashInput (selectedTwo S₁ S₂ proof) (j-secondStart S₁))
  else if j = backendStart S₁ S₂ then .statements proof.1
  else if j = backendStart S₁ S₂+1 then .empty
  else .responses proof.2.1 proof.2.2

def hashInput (proof : Proof S₁ S₂) (j : ℕ) : Domain S₁ S₂ :=
  if h : j < slots S₁ S₂ then
    Transcript.pointAt (context S₁ S₂ proof).1 (messages S₁ S₂ proof) ⟨j,h⟩
  else Transcript.pointAt (context S₁ S₂ proof).1 (messages S₁ S₂ proof)
    ⟨0, by unfold slots; omega⟩

abbrev points : PrefixPoints (Domain S₁ S₂) := Transcript.points

def key (p : Domain S₁ S₂) : Key := p.1

theorem hashInput_key (proof : Proof S₁ S₂) (j : ℕ) :
    key S₁ S₂ (hashInput S₁ S₂ proof j) = (context S₁ S₂ proof).1 := by
  unfold hashInput
  split_ifs <;> rfl

theorem slot_hashInput (proof : Proof S₁ S₂) (j : ℕ) (hj : j < slots S₁ S₂) :
    (points S₁ S₂).slot (hashInput S₁ S₂ proof j) = j := by
  rw [hashInput, dif_pos hj]
  rfl

theorem prefix_answers (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (j : ℕ) (hj : j < slots S₁ S₂) (i : Fin j) :
    (points S₁ S₂).chal H (hashInput S₁ S₂ proof j)
      ⟨i.val, by rw [slot_hashInput _ _ _ _ hj]; exact i.isLt⟩ =
      H (hashInput S₁ S₂ proof i.val) := by
  change H ((points S₁ S₂).anc (hashInput S₁ S₂ proof j) i.val) = _
  simp only [hashInput, dif_pos hj, dif_pos (i.isLt.trans hj), points,
    Transcript.points, Transcript.ancestor, Transcript.pointAt, dif_pos i.isLt]

/-- The two local schedules map their opening slots to the same global slot. -/
def firstSlot (j : ℕ) : ℕ :=
  if j < Side.steps S₁ then 1+j
  else if j = Side.steps S₁ then backendStart S₁ S₂ else backendStart S₁ S₂+2

def secondSlot (j : ℕ) : ℕ :=
  if j < Side.steps S₂ then secondStart S₁+j
  else if j = Side.steps S₂ then backendStart S₁ S₂+1 else backendStart S₁ S₂+2

def firstOracle (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂) (p : S₁.Domain) : C :=
  H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ (S₁.points.slot p)))

def secondOracle (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂) (p : S₂.Domain) : C :=
  H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ (S₂.points.slot p)))

theorem firstOracle_at (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (j : ℕ) (hj : j < S₁.slots) :
    firstOracle S₁ S₂ H proof (S₁.hashInput (selectedOne S₁ S₂ proof) j) =
      H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j)) := by
  rw [firstOracle, S₁.slot_hashInput _ _ hj]

theorem secondOracle_at (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (j : ℕ) (hj : j < S₂.slots) :
    secondOracle S₁ S₂ H proof (S₂.hashInput (selectedTwo S₁ S₂ proof) j) =
      H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j)) := by
  rw [secondOracle, S₂.slot_hashInput _ _ hj]

theorem firstOracle_prefix (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (p : S₁.Domain) (j : Fin (S₁.points.slot p)) :
    S₁.points.chal (firstOracle S₁ S₂ H proof) p j =
      H (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j.val)) := by
  change H (hashInput _ _ _ (firstSlot _ _ (S₁.points.slot (S₁.points.anc p j.val)))) = _
  rw [Side.ancestor_slot S₁ p j.val j.isLt]

theorem secondOracle_prefix (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (p : S₂.Domain) (j : Fin (S₂.points.slot p)) :
    S₂.points.chal (secondOracle S₁ S₂ H proof) p j =
      H (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j.val)) := by
  change H (hashInput _ _ _ (secondSlot _ _ (S₂.points.slot (S₂.points.anc p j.val)))) = _
  rw [Side.ancestor_slot S₂ p j.val j.isLt]

theorem firstSlot_lt (j : ℕ) (_ : j < S₁.slots) :
    firstSlot S₁ S₂ j < slots S₁ S₂ := by
  have hs := Side.steps_add_two S₁
  unfold firstSlot slots backendStart secondStart
  split_ifs <;> omega

theorem secondSlot_lt (j : ℕ) (_ : j < S₂.slots) :
    secondSlot S₁ S₂ j < slots S₁ S₂ := by
  have hs := Side.steps_add_two S₂
  unfold secondSlot slots backendStart secondStart
  split_ifs <;> omega

theorem firstSlot_strict (i j : ℕ) (hij : i < j) (hj : j < S₁.slots) :
    firstSlot S₁ S₂ i < firstSlot S₁ S₂ j := by
  have hs := Side.steps_add_two S₁
  unfold firstSlot backendStart secondStart
  split_ifs <;> omega

theorem secondSlot_strict (i j : ℕ) (hij : i < j) (hj : j < S₂.slots) :
    secondSlot S₁ S₂ i < secondSlot S₁ S₂ j := by
  have hs := Side.steps_add_two S₂
  unfold secondSlot backendStart secondStart
  split_ifs <;> omega

theorem hashInput_injective (proof : Proof S₁ S₂) :
    Function.Injective (fun i : Fin (slots S₁ S₂) => hashInput S₁ S₂ proof i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points S₁ S₂).slot heq
  simpa only [slot_hashInput _ _ _ _ i.isLt, slot_hashInput _ _ _ _ j.isLt] using h

/-- Read only a message already in the point's prefix. A malformed prefix
cannot supply a statement from a future position. -/
def messageAt (p : Domain S₁ S₂) (j : ℕ) : Option (Message S₁ S₂) :=
  if h : j < p.2.1.val + 1 then some (p.2.2 ⟨j,h⟩) else none

def current (p : Domain S₁ S₂) : Message S₁ S₂ := p.2.2 ⟨p.2.1.val, by omega⟩

def statementsAt (p : Domain S₁ S₂) : Option (Frontends S₁ S₂) :=
  match messageAt S₁ S₂ p (backendStart S₁ S₂) with
  | some (.statements frontends) => some frontends
  | _ => none

/-- Backend statements are recovered from the first backend point at both
later roles. They cannot be replaced after the first field challenge. -/
def localOne (p : Domain S₁ S₂) : Option S₁.Domain :=
  if 0 < (points S₁ S₂).slot p ∧ (points S₁ S₂).slot p < secondStart S₁ then
    match current S₁ S₂ p with | .first x => some x | _ => none
  else if (points S₁ S₂).slot p = backendStart S₁ S₂ then
    (statementsAt S₁ S₂ p).map fun f => Layered.Runtime.Replay.backend circuit₁ I₁ f.1.1
  else if (points S₁ S₂).slot p = backendStart S₁ S₂ + 2 then
    match statementsAt S₁ S₂ p, current S₁ S₂ p with
    | some f, .responses r _ => some (Layered.Runtime.Replay.opening circuit₁ I₁ f.1.1 r)
    | _, _ => none
  else none

def localTwo (p : Domain S₁ S₂) : Option S₂.Domain :=
  if secondStart S₁ ≤ (points S₁ S₂).slot p ∧ (points S₁ S₂).slot p < backendStart S₁ S₂ then
    match current S₁ S₂ p with | .second x => some x | _ => none
  else if (points S₁ S₂).slot p = backendStart S₁ S₂ + 1 then
    (statementsAt S₁ S₂ p).map fun f => Layered.Runtime.Replay.backend circuit₂ I₂ f
  else if (points S₁ S₂).slot p = backendStart S₁ S₂ + 2 then
    match statementsAt S₁ S₂ p, current S₁ S₂ p with
    | some f, .responses _ r => some (Layered.Runtime.Replay.opening circuit₂ I₂ f r)
    | _, _ => none
  else none

theorem current_at (proof : Proof S₁ S₂) (j : ℕ) (hj : j < slots S₁ S₂) :
    current S₁ S₂ (hashInput S₁ S₂ proof j) = messages S₁ S₂ proof j := by
  unfold current
  rw [hashInput, dif_pos hj]
  rfl

theorem messageAt_at (proof : Proof S₁ S₂) (i j : ℕ)
    (hj : j < slots S₁ S₂) (hij : i ≤ j) :
    messageAt S₁ S₂ (hashInput S₁ S₂ proof j) i = some (messages S₁ S₂ proof i) := by
  unfold messageAt
  rw [hashInput, dif_pos hj]
  simp only [Transcript.pointAt, dif_pos (show i < j+1 by omega)]

theorem statementsAt_at (proof : Proof S₁ S₂) (j : ℕ)
    (hj : j < slots S₁ S₂) (hback : backendStart S₁ S₂ ≤ j) :
    statementsAt S₁ S₂ (hashInput S₁ S₂ proof j) = some proof.1 := by
  rw [statementsAt, messageAt_at _ _ _ _ _ hj hback]
  have hb : 0 < backendStart S₁ S₂ := by unfold backendStart secondStart; omega
  simp only [messages, if_neg (Nat.ne_of_gt hb),
    if_neg (show ¬ backendStart S₁ S₂ < secondStart S₁ by unfold backendStart; omega),
    lt_self_iff_false, if_false, if_true]

/-- Local algebra reads its earlier coins at their new global positions.
The default is used only for malformed points that ask for a future coin. -/
def firstPrefix (p : Domain S₁ S₂) (pref : Fin ((points S₁ S₂).slot p) → C)
    (x : S₁.Domain) : Fin (S₁.points.slot x) → C :=
  fun j => LfzkV2.Replay.fillAnswers S₁.dflt pref (firstSlot S₁ S₂ j.val)

def secondPrefix (p : Domain S₁ S₂) (pref : Fin ((points S₁ S₂).slot p) → C)
    (x : S₂.Domain) : Fin (S₂.points.slot x) → C :=
  fun j => LfzkV2.Replay.fillAnswers S₂.dflt pref (secondSlot S₁ S₂ j.val)

theorem firstPrefix_at (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (j : ℕ) (hj : j < S₁.slots) :
    let p := hashInput S₁ S₂ proof (firstSlot S₁ S₂ j)
    let x := S₁.hashInput (selectedOne S₁ S₂ proof) j
    firstPrefix S₁ S₂ p ((points S₁ S₂).chal H p) x =
      S₁.points.chal (firstOracle S₁ S₂ H proof) x := by
  intro p x
  funext i
  have hi : i.val < j := by simpa only [x, S₁.slot_hashInput _ _ hj] using i.isLt
  have hmap := firstSlot_strict S₁ S₂ i.val j hi hj
  have hslot := slot_hashInput S₁ S₂ proof _ (firstSlot_lt S₁ S₂ j hj)
  rw [firstPrefix, LfzkV2.Replay.fillAnswers,
    dif_pos (by simpa only [p, hslot] using hmap)]
  rw [firstOracle_prefix]
  exact prefix_answers S₁ S₂ H proof _ (firstSlot_lt S₁ S₂ j hj) ⟨_, hmap⟩

theorem secondPrefix_at (H : Domain S₁ S₂ → C) (proof : Proof S₁ S₂)
    (j : ℕ) (hj : j < S₂.slots) :
    let p := hashInput S₁ S₂ proof (secondSlot S₁ S₂ j)
    let x := S₂.hashInput (selectedTwo S₁ S₂ proof) j
    secondPrefix S₁ S₂ p ((points S₁ S₂).chal H p) x =
      S₂.points.chal (secondOracle S₁ S₂ H proof) x := by
  intro p x
  funext i
  have hi : i.val < j := by simpa only [x, S₂.slot_hashInput _ _ hj] using i.isLt
  have hmap := secondSlot_strict S₁ S₂ i.val j hi hj
  have hslot := slot_hashInput S₁ S₂ proof _ (secondSlot_lt S₁ S₂ j hj)
  rw [secondPrefix, LfzkV2.Replay.fillAnswers,
    dif_pos (by simpa only [p, hslot] using hmap)]
  rw [secondOracle_prefix]
  exact prefix_answers S₁ S₂ H proof _ (secondSlot_lt S₁ S₂ j hj) ⟨_, hmap⟩

theorem localOne_front (proof : Proof S₁ S₂) (j : ℕ) (hj : j < Side.steps S₁) :
    localOne S₁ S₂ (hashInput S₁ S₂ proof (1+j)) =
      some (S₁.hashInput (selectedOne S₁ S₂ proof) j) := by
  have hs : 1+j < slots S₁ S₂ := by unfold slots backendStart secondStart; omega
  have hslot := slot_hashInput S₁ S₂ proof _ hs
  unfold localOne
  change (if 0 < (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < secondStart S₁ then _ else _) = _
  rw [hslot, if_pos (by unfold secondStart; omega), current_at _ _ _ _ hs]
  simp only [messages, if_neg (by omega : 1+j ≠ 0),
    if_pos (by unfold secondStart; omega : 1+j < secondStart S₁), Nat.add_sub_cancel_left]

theorem localTwo_front (proof : Proof S₁ S₂) (j : ℕ) (hj : j < Side.steps S₂) :
    localTwo S₁ S₂ (hashInput S₁ S₂ proof (secondStart S₁+j)) =
      some (S₂.hashInput (selectedTwo S₁ S₂ proof) j) := by
  have hs : secondStart S₁+j < slots S₁ S₂ := by unfold slots backendStart; omega
  have hslot := slot_hashInput S₁ S₂ proof _ hs
  unfold localTwo
  change (if secondStart S₁ ≤ (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < backendStart S₁ S₂ then _ else _) = _
  rw [hslot, if_pos (by unfold backendStart; omega), current_at _ _ _ _ hs]
  simp only [messages, if_neg (by unfold secondStart; omega : secondStart S₁+j ≠ 0),
    if_neg (by omega : ¬ secondStart S₁+j < secondStart S₁),
    if_pos (by unfold backendStart; omega : secondStart S₁+j < backendStart S₁ S₂), Nat.add_sub_cancel_left]

theorem localOne_backend (proof : Proof S₁ S₂) :
    localOne S₁ S₂ (hashInput S₁ S₂ proof (backendStart S₁ S₂)) =
      some (S₁.hashInput (selectedOne S₁ S₂ proof) (Side.steps S₁)) := by
  have hs : backendStart S₁ S₂ < slots S₁ S₂ := by unfold slots; omega
  rw [Side.backend_at]
  unfold localOne
  change (if 0 < (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < secondStart S₁ then _ else _) = _
  rw [slot_hashInput _ _ _ _ hs, if_neg (by unfold backendStart; omega), if_pos rfl,
    statementsAt_at _ _ _ _ hs le_rfl]
  rfl

theorem localTwo_backend (proof : Proof S₁ S₂) :
    localTwo S₁ S₂ (hashInput S₁ S₂ proof (backendStart S₁ S₂+1)) =
      some (S₂.hashInput (selectedTwo S₁ S₂ proof) (Side.steps S₂)) := by
  have hs : backendStart S₁ S₂+1 < slots S₁ S₂ := by unfold slots; omega
  rw [Side.backend_at]
  unfold localTwo
  change (if secondStart S₁ ≤ (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < backendStart S₁ S₂ then _ else _) = _
  rw [slot_hashInput _ _ _ _ hs, if_neg (by omega), if_pos rfl,
    statementsAt_at _ _ _ _ hs (by omega)]
  rfl

theorem current_opening (proof : Proof S₁ S₂) :
    current S₁ S₂ (hashInput S₁ S₂ proof (backendStart S₁ S₂+2)) =
      .responses proof.2.1 proof.2.2 := by
  rw [current_at _ _ _ _ (by unfold slots; omega)]
  simp only [messages, if_neg (by omega : backendStart S₁ S₂+2 ≠ 0),
    if_neg (by unfold backendStart; omega : ¬ backendStart S₁ S₂+2 < secondStart S₁),
    if_neg (by omega : ¬ backendStart S₁ S₂+2 < backendStart S₁ S₂),
    if_neg (by omega : backendStart S₁ S₂+2 ≠ backendStart S₁ S₂),
    if_neg (by omega : backendStart S₁ S₂+2 ≠ backendStart S₁ S₂+1)]

theorem localOne_opening (proof : Proof S₁ S₂) :
    localOne S₁ S₂ (hashInput S₁ S₂ proof (backendStart S₁ S₂+2)) =
      some (S₁.hashInput (selectedOne S₁ S₂ proof) (Side.steps S₁+1)) := by
  have hs : backendStart S₁ S₂+2 < slots S₁ S₂ := by unfold slots; omega
  rw [Side.opening_at]
  unfold localOne
  change (if 0 < (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < secondStart S₁ then _ else _) = _
  rw [slot_hashInput _ _ _ _ hs, if_neg (by unfold backendStart; omega),
    if_neg (by omega), if_pos rfl, statementsAt_at _ _ _ _ hs (by omega), current_opening]
  rfl

theorem localTwo_opening (proof : Proof S₁ S₂) :
    localTwo S₁ S₂ (hashInput S₁ S₂ proof (backendStart S₁ S₂+2)) =
      some (S₂.hashInput (selectedTwo S₁ S₂ proof) (Side.steps S₂+1)) := by
  have hs : backendStart S₁ S₂+2 < slots S₁ S₂ := by unfold slots; omega
  rw [Side.opening_at]
  unfold localTwo
  change (if secondStart S₁ ≤ (points S₁ S₂).slot _ ∧ (points S₁ S₂).slot _ < backendStart S₁ S₂ then _ else _) = _
  rw [slot_hashInput _ _ _ _ hs, if_neg (by omega),
    if_neg (by omega), if_pos rfl, statementsAt_at _ _ _ _ hs (by omega), current_opening]
  rfl

theorem localOne_at (proof : Proof S₁ S₂) (j : ℕ) (hj : j < S₁.slots) :
    localOne S₁ S₂ (hashInput S₁ S₂ proof (firstSlot S₁ S₂ j)) =
      some (S₁.hashInput (selectedOne S₁ S₂ proof) j) := by
  have hs := Side.steps_add_two S₁
  unfold firstSlot
  split_ifs with hfront hback
  · exact localOne_front S₁ S₂ proof j hfront
  · subst j; exact localOne_backend S₁ S₂ proof
  · have heq : j = Side.steps S₁+1 := by omega
    subst j; exact localOne_opening S₁ S₂ proof

theorem localTwo_at (proof : Proof S₁ S₂) (j : ℕ) (hj : j < S₂.slots) :
    localTwo S₁ S₂ (hashInput S₁ S₂ proof (secondSlot S₁ S₂ j)) =
      some (S₂.hashInput (selectedTwo S₁ S₂ proof) j) := by
  have hs := Side.steps_add_two S₂
  unfold secondSlot
  split_ifs with hfront hback
  · exact localTwo_front S₁ S₂ proof j hfront
  · subst j; exact localTwo_backend S₁ S₂ proof
  · have heq : j = Side.steps S₂+1 := by omega
    subst j; exact localTwo_opening S₁ S₂ proof

def firstIndex (j : Fin S₁.slots) : Fin (slots S₁ S₂) :=
  ⟨firstSlot S₁ S₂ j.val, firstSlot_lt S₁ S₂ j.val j.isLt⟩

def secondIndex (j : Fin S₂.slots) : Fin (slots S₁ S₂) :=
  ⟨secondSlot S₁ S₂ j.val, secondSlot_lt S₁ S₂ j.val j.isLt⟩

theorem firstIndex_injective : Function.Injective (firstIndex S₁ S₂) := by
  intro i j heq
  apply Fin.ext
  have he := congrArg Fin.val heq
  change firstSlot S₁ S₂ i.val = firstSlot S₁ S₂ j.val at he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (Nat.ne_of_lt (firstSlot_strict S₁ S₂ _ _ h j.isLt)) he
  · exact (Nat.ne_of_lt (firstSlot_strict S₁ S₂ _ _ h i.isLt)) he.symm

theorem secondIndex_injective : Function.Injective (secondIndex S₁ S₂) := by
  intro i j heq
  apply Fin.ext
  have he := congrArg Fin.val heq
  change secondSlot S₁ S₂ i.val = secondSlot S₁ S₂ j.val at he
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (Nat.ne_of_lt (secondSlot_strict S₁ S₂ _ _ h j.isLt)) he
  · exact (Nat.ne_of_lt (secondSlot_strict S₁ S₂ _ _ h i.isLt)) he.symm

theorem localOne_none_off (p : Domain S₁ S₂)
    (hoff : ∀ j : Fin S₁.slots, firstSlot S₁ S₂ j.val ≠ (points S₁ S₂).slot p) :
    localOne S₁ S₂ p = none := by
  have hs := Side.steps_add_two S₁
  unfold localOne
  split_ifs with hfront hback hopen
  · have hj : (points S₁ S₂).slot p-1 < Side.steps S₁ := by unfold secondStart at hfront; omega
    have h := hoff ⟨(points S₁ S₂).slot p-1,by omega⟩
    simp only [firstSlot, if_pos hj] at h
    omega
  · have h := hoff ⟨Side.steps S₁,by omega⟩
    simp only [firstSlot, lt_self_iff_false, if_false, if_true] at h
    exact (h hback.symm).elim
  · have h := hoff ⟨Side.steps S₁+1,by omega⟩
    simp only [firstSlot, if_neg (by omega : ¬ Side.steps S₁+1 < Side.steps S₁),
      if_neg (by omega : Side.steps S₁+1 ≠ Side.steps S₁)] at h
    exact (h hopen.symm).elim
  · rfl

theorem localTwo_none_off (p : Domain S₁ S₂)
    (hoff : ∀ j : Fin S₂.slots, secondSlot S₁ S₂ j.val ≠ (points S₁ S₂).slot p) :
    localTwo S₁ S₂ p = none := by
  have hs := Side.steps_add_two S₂
  unfold localTwo
  split_ifs with hfront hback hopen
  · have hj : (points S₁ S₂).slot p-secondStart S₁ < Side.steps S₂ := by unfold backendStart at hfront; omega
    have h := hoff ⟨(points S₁ S₂).slot p-secondStart S₁,by omega⟩
    simp only [secondSlot, if_pos hj] at h
    omega
  · have h := hoff ⟨Side.steps S₂,by omega⟩
    simp only [secondSlot, lt_self_iff_false, if_false, if_true] at h
    exact (h hback.symm).elim
  · have h := hoff ⟨Side.steps S₂+1,by omega⟩
    simp only [secondSlot, if_neg (by omega : ¬ Side.steps S₂+1 < Side.steps S₂),
      if_neg (by omega : Side.steps S₂+1 ≠ Side.steps S₂)] at h
    exact (h hopen.symm).elim
  · rfl

end LfzkV2.Layered.Joint.Replay
