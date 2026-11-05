import LfzkV2.GradedReplay

/-!
# Packing between the frontend and backend challenges

The packing point carries the complete frontend payload and `U`, represented
by `Parent`. It cannot carry the later scalar response `A`: the backend point
adds that response, and the opening point adds the backend response. The
optional packing stage is absent from the degree-one verifier schedule.

The circuit argument is used only for the shared message-prefix geometry.
Native semantics are supplied by the native replay, never by this shape.
-/

namespace LfzkV2.Packed.Replay

open RecursivePolygero Bcs.TotalOracle
open scoped Classical

variable {F C Key Parent : Type} [Field F] [Fintype F] [DecidableEq F]
variable {out input : ℕ}

abbrev Roles (I : Instance F) (Parent : Type) :=
  Parent ⊕ (Parent × F) ⊕ ((Parent × F) × I.layer.Payload)

abbrev Domain (Key : Type) (shape : Circuit F out input) (I : Instance F) (Parent : Type) :=
  LfzkV2.Replay.Point Key F shape ⊕ Roles I Parent

abbrev Selected (I : Instance F) (Parent : Type) := (Parent × F) × I.layer.Payload

def packingSlots (packed : Bool) : ℕ := if packed then 1 else 0

variable (shape : Circuit F out input) (I : Instance F)
variable (packed : Bool) (keyOf : Parent → Key) (payloadOf : Parent → LfzkV2.Replay.Payload shape)

def packing (p : Parent) : Domain Key shape I Parent := .inr (.inl p)
def backend (p : Parent × F) : Domain Key shape I Parent := .inr (.inr (.inl p))
def opening (p : Parent × F) (response : I.layer.Payload) : Domain Key shape I Parent :=
  .inr (.inr (.inr (p,response)))

def key : Domain Key shape I Parent → Key
  | .inl p => p.1
  | .inr (.inl p) => keyOf p
  | .inr (.inr (.inl p)) => keyOf p.1
  | .inr (.inr (.inr (p,_))) => keyOf p.1

def points : PrefixPoints (Domain Key shape I Parent) where
  slot
    | .inl p => (LfzkV2.Replay.points shape).slot p
    | .inr (.inl _) => LfzkV2.Replay.slots shape
    | .inr (.inr (.inl _)) => LfzkV2.Replay.slots shape + packingSlots packed
    | .inr (.inr (.inr _)) => LfzkV2.Replay.slots shape + packingSlots packed + 1
  anc x j := match x with
    | .inl p => .inl ((LfzkV2.Replay.points shape).anc p j)
    | .inr (.inl p) => .inl (LfzkV2.Replay.hashInput shape (keyOf p) (payloadOf p) j)
    | .inr (.inr (.inl p)) => if j < LfzkV2.Replay.slots shape then
        .inl (LfzkV2.Replay.hashInput shape (keyOf p.1) (payloadOf p.1) j)
      else packing shape I p.1
    | .inr (.inr (.inr (p,_))) => if j < LfzkV2.Replay.slots shape then
        .inl (LfzkV2.Replay.hashInput shape (keyOf p.1) (payloadOf p.1) j)
      else if packed && j == LfzkV2.Replay.slots shape then packing shape I p.1
      else backend shape I p
  anc_ne x j hj := by
    rcases x with p | p | p | ⟨p,response⟩
    · intro heq
      exact (LfzkV2.Replay.points shape).anc_ne p j hj (Sum.inl.inj heq)
    · intro heq; cases heq
    · dsimp only
      split_ifs <;> intro heq <;> cases heq
    · dsimp only
      split_ifs <;> intro heq <;> cases heq

def hashInput (s : Selected I Parent) (j : ℕ) : Domain Key shape I Parent :=
  if j < LfzkV2.Replay.slots shape then
    .inl (LfzkV2.Replay.hashInput shape (keyOf s.1.1) (payloadOf s.1.1) j)
  else if packed && j == LfzkV2.Replay.slots shape then packing shape I s.1.1
  else if j = LfzkV2.Replay.slots shape + packingSlots packed then backend shape I s.1
  else opening shape I s.1 s.2

theorem hashInput_key (s : Selected I Parent) (j : ℕ) :
    key shape I keyOf (hashInput shape I packed keyOf payloadOf s j) = keyOf s.1.1 := by
  unfold hashInput
  split_ifs
  · exact LfzkV2.Replay.hashInput_key shape _ _ _
  · rfl
  · rfl
  · rfl

theorem slot_hashInput (s : Selected I Parent) (j : ℕ)
    (hj : j < LfzkV2.Replay.slots shape + packingSlots packed + 2) :
    (points shape I packed keyOf payloadOf).slot
      (hashInput shape I packed keyOf payloadOf s j) = j := by
  unfold hashInput
  split_ifs with hfront hpack hback
  · rw [LfzkV2.Replay.hashInput_at shape _ _ ⟨j,hfront⟩]
    rfl
  · cases packed <;> simp_all [packingSlots, points, packing]
  · exact hback.symm
  · cases packed <;> simp_all [packingSlots, points, opening] <;> omega

theorem hashInput_injective (s : Selected I Parent) :
    Function.Injective (fun i : Fin (LfzkV2.Replay.slots shape + packingSlots packed + 2) =>
      hashInput shape I packed keyOf payloadOf s i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points shape I packed keyOf payloadOf).slot heq
  simpa only [slot_hashInput shape I packed keyOf payloadOf s _ i.isLt,
    slot_hashInput shape I packed keyOf payloadOf s _ j.isLt] using h

theorem frontend_prefix (H : Domain Key shape I Parent → C) (k : Key)
    (payload : LfzkV2.Replay.Payload shape) (i : Fin (LfzkV2.Replay.slots shape)) :
    (points shape I packed keyOf payloadOf).chal H
        (.inl (LfzkV2.Replay.pointAt shape k payload i)) =
      fun j : Fin i.val => H (.inl (LfzkV2.Replay.hashInput shape k payload j.val)) :=
  LfzkV2.Replay.prefix_answers shape (fun p => H (.inl p)) k payload i

theorem packing_prefix (H : Domain Key shape I Parent → C) (p : Parent) :
    (points shape I packed keyOf payloadOf).chal H (packing shape I p) =
      fun j : Fin (LfzkV2.Replay.slots shape) =>
        H (.inl (LfzkV2.Replay.hashInput shape (keyOf p) (payloadOf p) j.val)) := rfl

theorem backend_prefix (H : Domain Key shape I Parent → C) (p : Parent × F)
    (j : Fin (LfzkV2.Replay.slots shape + packingSlots packed)) :
    (points shape I packed keyOf payloadOf).chal H (backend shape I p) j =
      if j.val < LfzkV2.Replay.slots shape then
        H (.inl (LfzkV2.Replay.hashInput shape (keyOf p.1) (payloadOf p.1) j.val))
      else H (packing shape I p.1) := by
  dsimp only [PrefixPoints.chal, points, backend]
  split_ifs <;> rfl

theorem opening_prefix (H : Domain Key shape I Parent → C) (p : Parent × F)
    (response : I.layer.Payload)
    (j : Fin (LfzkV2.Replay.slots shape + packingSlots packed + 1)) :
    (points shape I packed keyOf payloadOf).chal H (opening shape I p response) j =
      if j.val < LfzkV2.Replay.slots shape then
        H (.inl (LfzkV2.Replay.hashInput shape (keyOf p.1) (payloadOf p.1) j.val))
      else if packed && j.val == LfzkV2.Replay.slots shape then H (packing shape I p.1)
      else H (backend shape I p) := by
  dsimp only [PrefixPoints.chal, points, opening]
  split_ifs <;> rfl

theorem opening_coin (H : Domain Key shape I Parent → C) (p : Parent × F)
    (response : I.layer.Payload) :
    (points shape I packed keyOf payloadOf).chal H (opening shape I p response)
      ⟨LfzkV2.Replay.slots shape + packingSlots packed, by change _ < _ + 1; omega⟩ =
      H (backend shape I p) := by
  rw [opening_prefix]
  cases packed <;> simp [packingSlots]

theorem backend_at (s : Selected I Parent) :
    hashInput shape I packed keyOf payloadOf s
      (LfzkV2.Replay.slots shape + packingSlots packed) = backend shape I s.1 := by
  cases packed <;> simp [hashInput, packingSlots]

theorem opening_at (s : Selected I Parent) :
    hashInput shape I packed keyOf payloadOf s
      (LfzkV2.Replay.slots shape + packingSlots packed + 1) = opening shape I s.1 s.2 := by
  cases packed <;> simp [hashInput, packingSlots, show
    ¬ LfzkV2.Replay.slots shape + 1 + 1 < LfzkV2.Replay.slots shape by omega,
    show LfzkV2.Replay.slots shape + 1 + 1 ≠ LfzkV2.Replay.slots shape by omega]

theorem packing_at (s : Selected I Parent) :
    hashInput shape I true keyOf payloadOf s (LfzkV2.Replay.slots shape) =
      packing shape I s.1.1 := by simp [hashInput]

/-- The complete statement prefix includes delta exactly when packing is enabled. -/
def statementAnswers (H : Domain Key shape I Parent → C) (p : Parent) (j : ℕ) : C :=
  if j < LfzkV2.Replay.slots shape then
    H (.inl (LfzkV2.Replay.hashInput shape (keyOf p) (payloadOf p) j))
  else H (packing shape I p)

variable {View : Type}

def viewAt (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (p : Parent × F) {m : ℕ} (pref : Fin m → C) : View :=
  view p (LfzkV2.Replay.fillAnswers dflt pref)

theorem backend_view_eq (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (hprefix : ∀ p first second,
      (∀ j, j < LfzkV2.Replay.slots shape + packingSlots packed → first j = second j) →
      view p first = view p second)
    (H : Domain Key shape I Parent → C) (p : Parent × F) :
    viewAt view dflt p ((points shape I packed keyOf payloadOf).chal H (backend shape I p)) =
      view p (statementAnswers shape I keyOf payloadOf H p.1) := by
  apply hprefix
  intro j hj
  rw [LfzkV2.Replay.fillAnswers, dif_pos (show j <
    (points shape I packed keyOf payloadOf).slot (backend shape I p) from hj), backend_prefix]
  rfl

theorem opening_view_eq (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (hprefix : ∀ p first second,
      (∀ j, j < LfzkV2.Replay.slots shape + packingSlots packed → first j = second j) →
      view p first = view p second)
    (H : Domain Key shape I Parent → C) (p : Parent × F) (response : I.layer.Payload) :
    viewAt view dflt p ((points shape I packed keyOf payloadOf).chal H (opening shape I p response)) =
      view p (statementAnswers shape I keyOf payloadOf H p.1) := by
  apply hprefix
  intro j hj
  rw [LfzkV2.Replay.fillAnswers, dif_pos (by change j < _ + 1; omega), opening_prefix]
  unfold statementAnswers
  split_ifs with hfront hpack
  · rfl
  · rfl
  · exfalso
    change ¬ j < LfzkV2.Replay.slots shape at hfront
    change ¬ (packed && j == LfzkV2.Replay.slots shape) = true at hpack
    cases packed with
    | false =>
      change j < LfzkV2.Replay.slots shape + 0 at hj
      omega
    | true =>
      change j < LfzkV2.Replay.slots shape + 1 at hj
      have heq : j = LfzkV2.Replay.slots shape := by omega
      exact hpack (by simp [heq])

end LfzkV2.Packed.Replay
