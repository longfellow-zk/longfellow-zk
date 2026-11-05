import LfzkV2.GradedReplay
import LfzkV2.Layered.Sampling

/-!
# Packing between the frontend and backend challenges

The packing point carries the complete frontend payload and `U`, represented
by `Parent`. It cannot carry the later scalar response `A`: the backend point
adds that response, and the opening point adds the backend response. The
optional packing stage is absent from the degree-one verifier schedule.

This wrapper extends the linear-terminal frontend schedule with packing
and backend roles. The frontend replay supplies the layered circuit semantics.
-/

namespace LfzkV2.Layered.Runtime.Replay

open RecursivePolygero Bcs.TotalOracle
open scoped Classical

variable {F C Key Parent : Type} [Field F] [Fintype F] [DecidableEq F]
variable {out input : ℕ}

abbrev Roles (I : Instance F) (Parent : Type) :=
  Parent ⊕ (Parent × F) ⊕ ((Parent × F) × I.layer.Payload)

abbrev Domain (Key : Type) (circuit : Layered.Circuit F out input) (I : Instance F) (Parent : Type) :=
  LfzkV2.Layered.Replay.Point Key F circuit ⊕ Roles I Parent

abbrev Selected (I : Instance F) (Parent : Type) := (Parent × F) × I.layer.Payload

def packingSlots (packed : Bool) : ℕ := if packed then 1 else 0

variable (circuit : Layered.Circuit F out input) (I : Instance F)
variable (packed : Bool) (keyOf : Parent → Key) (payloadOf : Parent → LfzkV2.Layered.Replay.Payload circuit)

def packing (p : Parent) : Domain Key circuit I Parent := .inr (.inl p)
def backend (p : Parent × F) : Domain Key circuit I Parent := .inr (.inr (.inl p))
def opening (p : Parent × F) (response : I.layer.Payload) : Domain Key circuit I Parent :=
  .inr (.inr (.inr (p,response)))

def key : Domain Key circuit I Parent → Key
  | .inl p => p.1
  | .inr (.inl p) => keyOf p
  | .inr (.inr (.inl p)) => keyOf p.1
  | .inr (.inr (.inr (p,_))) => keyOf p.1

def points : PrefixPoints (Domain Key circuit I Parent) where
  slot
    | .inl p => (LfzkV2.Layered.Replay.points circuit).slot p
    | .inr (.inl _) => LfzkV2.Layered.Replay.slots circuit
    | .inr (.inr (.inl _)) => LfzkV2.Layered.Replay.slots circuit + packingSlots packed
    | .inr (.inr (.inr _)) => LfzkV2.Layered.Replay.slots circuit + packingSlots packed + 1
  anc x j := match x with
    | .inl p => .inl ((LfzkV2.Layered.Replay.points circuit).anc p j)
    | .inr (.inl p) => .inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p) (payloadOf p) j)
    | .inr (.inr (.inl p)) => if j < LfzkV2.Layered.Replay.slots circuit then
        .inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p.1) (payloadOf p.1) j)
      else packing circuit I p.1
    | .inr (.inr (.inr (p,_))) => if j < LfzkV2.Layered.Replay.slots circuit then
        .inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p.1) (payloadOf p.1) j)
      else if packed && j == LfzkV2.Layered.Replay.slots circuit then packing circuit I p.1
      else backend circuit I p
  anc_ne x j hj := by
    rcases x with p | p | p | ⟨p,response⟩
    · intro heq
      exact (LfzkV2.Layered.Replay.points circuit).anc_ne p j hj (Sum.inl.inj heq)
    · intro heq; cases heq
    · dsimp only
      split_ifs <;> intro heq <;> cases heq
    · dsimp only
      split_ifs <;> intro heq <;> cases heq

def hashInput (s : Selected I Parent) (j : ℕ) : Domain Key circuit I Parent :=
  if j < LfzkV2.Layered.Replay.slots circuit then
    .inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf s.1.1) (payloadOf s.1.1) j)
  else if packed && j == LfzkV2.Layered.Replay.slots circuit then packing circuit I s.1.1
  else if j = LfzkV2.Layered.Replay.slots circuit + packingSlots packed then backend circuit I s.1
  else opening circuit I s.1 s.2

theorem hashInput_key (s : Selected I Parent) (j : ℕ) :
    key circuit I keyOf (hashInput circuit I packed keyOf payloadOf s j) = keyOf s.1.1 := by
  unfold hashInput
  split_ifs
  · exact LfzkV2.Layered.Replay.hashInput_key circuit _ _ _
  · rfl
  · rfl
  · rfl

theorem slot_hashInput (s : Selected I Parent) (j : ℕ)
    (hj : j < LfzkV2.Layered.Replay.slots circuit + packingSlots packed + 2) :
    (points circuit I packed keyOf payloadOf).slot
      (hashInput circuit I packed keyOf payloadOf s j) = j := by
  unfold hashInput
  split_ifs with hfront hpack hback
  · rw [LfzkV2.Layered.Replay.hashInput_at circuit _ _ ⟨j,hfront⟩]
    rfl
  · cases packed <;> simp_all [packingSlots, points, packing]
  · exact hback.symm
  · cases packed <;> simp_all [packingSlots, points, opening] <;> omega

theorem hashInput_injective (s : Selected I Parent) :
    Function.Injective (fun i : Fin (LfzkV2.Layered.Replay.slots circuit + packingSlots packed + 2) =>
      hashInput circuit I packed keyOf payloadOf s i.val) := by
  intro i j heq
  apply Fin.ext
  have h := congrArg (points circuit I packed keyOf payloadOf).slot heq
  simpa only [slot_hashInput circuit I packed keyOf payloadOf s _ i.isLt,
    slot_hashInput circuit I packed keyOf payloadOf s _ j.isLt] using h

theorem frontend_prefix (H : Domain Key circuit I Parent → C) (k : Key)
    (payload : LfzkV2.Layered.Replay.Payload circuit) (i : Fin (LfzkV2.Layered.Replay.slots circuit)) :
    (points circuit I packed keyOf payloadOf).chal H
        (.inl (LfzkV2.Layered.Replay.pointAt circuit k payload i)) =
      fun j : Fin i.val => H (.inl (LfzkV2.Layered.Replay.hashInput circuit k payload j.val)) :=
  LfzkV2.Layered.Replay.prefix_answers circuit (fun p => H (.inl p)) k payload i

theorem packing_prefix (H : Domain Key circuit I Parent → C) (p : Parent) :
    (points circuit I packed keyOf payloadOf).chal H (packing circuit I p) =
      fun j : Fin (LfzkV2.Layered.Replay.slots circuit) =>
        H (.inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p) (payloadOf p) j.val)) := rfl

theorem backend_prefix (H : Domain Key circuit I Parent → C) (p : Parent × F)
    (j : Fin (LfzkV2.Layered.Replay.slots circuit + packingSlots packed)) :
    (points circuit I packed keyOf payloadOf).chal H (backend circuit I p) j =
      if j.val < LfzkV2.Layered.Replay.slots circuit then
        H (.inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p.1) (payloadOf p.1) j.val))
      else H (packing circuit I p.1) := by
  dsimp only [PrefixPoints.chal, points, backend]
  split_ifs <;> rfl

theorem opening_prefix (H : Domain Key circuit I Parent → C) (p : Parent × F)
    (response : I.layer.Payload)
    (j : Fin (LfzkV2.Layered.Replay.slots circuit + packingSlots packed + 1)) :
    (points circuit I packed keyOf payloadOf).chal H (opening circuit I p response) j =
      if j.val < LfzkV2.Layered.Replay.slots circuit then
        H (.inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p.1) (payloadOf p.1) j.val))
      else if packed && j.val == LfzkV2.Layered.Replay.slots circuit then H (packing circuit I p.1)
      else H (backend circuit I p) := by
  dsimp only [PrefixPoints.chal, points, opening]
  split_ifs <;> rfl

theorem opening_coin (H : Domain Key circuit I Parent → C) (p : Parent × F)
    (response : I.layer.Payload) :
    (points circuit I packed keyOf payloadOf).chal H (opening circuit I p response)
      ⟨LfzkV2.Layered.Replay.slots circuit + packingSlots packed, by change _ < _ + 1; omega⟩ =
      H (backend circuit I p) := by
  rw [opening_prefix]
  cases packed <;> simp [packingSlots]

theorem backend_at (s : Selected I Parent) :
    hashInput circuit I packed keyOf payloadOf s
      (LfzkV2.Layered.Replay.slots circuit + packingSlots packed) = backend circuit I s.1 := by
  cases packed <;> simp [hashInput, packingSlots]

theorem opening_at (s : Selected I Parent) :
    hashInput circuit I packed keyOf payloadOf s
      (LfzkV2.Layered.Replay.slots circuit + packingSlots packed + 1) = opening circuit I s.1 s.2 := by
  cases packed <;> simp [hashInput, packingSlots, show
    ¬ LfzkV2.Layered.Replay.slots circuit + 1 + 1 < LfzkV2.Layered.Replay.slots circuit by omega,
    show LfzkV2.Layered.Replay.slots circuit + 1 + 1 ≠ LfzkV2.Layered.Replay.slots circuit by omega]

theorem packing_at (s : Selected I Parent) :
    hashInput circuit I true keyOf payloadOf s (LfzkV2.Layered.Replay.slots circuit) =
      packing circuit I s.1.1 := by simp [hashInput]

/-- The complete statement prefix includes delta exactly when packing is enabled. -/
def statementAnswers (H : Domain Key circuit I Parent → C) (p : Parent) (j : ℕ) : C :=
  if j < LfzkV2.Layered.Replay.slots circuit then
    H (.inl (LfzkV2.Layered.Replay.hashInput circuit (keyOf p) (payloadOf p) j))
  else H (packing circuit I p)

variable {View : Type}

def viewAt (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (p : Parent × F) {m : ℕ} (pref : Fin m → C) : View :=
  view p (LfzkV2.Replay.fillAnswers dflt pref)

theorem backend_view_eq (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (hprefix : ∀ p first second,
      (∀ j, j < LfzkV2.Layered.Replay.slots circuit + packingSlots packed → first j = second j) →
      view p first = view p second)
    (H : Domain Key circuit I Parent → C) (p : Parent × F) :
    viewAt view dflt p ((points circuit I packed keyOf payloadOf).chal H (backend circuit I p)) =
      view p (statementAnswers circuit I keyOf payloadOf H p.1) := by
  apply hprefix
  intro j hj
  rw [LfzkV2.Replay.fillAnswers, dif_pos (show j <
    (points circuit I packed keyOf payloadOf).slot (backend circuit I p) from hj), backend_prefix]
  rfl

theorem opening_view_eq (view : Parent × F → (ℕ → C) → View) (dflt : C)
    (hprefix : ∀ p first second,
      (∀ j, j < LfzkV2.Layered.Replay.slots circuit + packingSlots packed → first j = second j) →
      view p first = view p second)
    (H : Domain Key circuit I Parent → C) (p : Parent × F) (response : I.layer.Payload) :
    viewAt view dflt p ((points circuit I packed keyOf payloadOf).chal H (opening circuit I p response)) =
      view p (statementAnswers circuit I keyOf payloadOf H p.1) := by
  apply hprefix
  intro j hj
  rw [LfzkV2.Replay.fillAnswers, dif_pos (by change j < _ + 1; omega), opening_prefix]
  unfold statementAnswers
  split_ifs with hfront hpack
  · rfl
  · rfl
  · exfalso
    change ¬ j < LfzkV2.Layered.Replay.slots circuit at hfront
    change ¬ (packed && j == LfzkV2.Layered.Replay.slots circuit) = true at hpack
    cases packed with
    | false =>
      change j < LfzkV2.Layered.Replay.slots circuit + 0 at hj
      omega
    | true =>
      change j < LfzkV2.Layered.Replay.slots circuit + 1 at hj
      have heq : j = LfzkV2.Layered.Replay.slots circuit := by omega
      exact hpack (by simp [heq])

end LfzkV2.Layered.Runtime.Replay
