import LfzkV2.Layered.Replay

/-! The schedule distinguishes the cross-message challenge from the later
claim-combining challenge. Each role has a unique slot and message prefix. -/

namespace LfzkV2.Layered.Replay

open SumcheckV2
open LfzkV2.Replay (vectorSlots)

variable {F : Type}

abbrev LayerRole : {out input : ℕ} → Layered.Circuit F out input → Type
  | _, _, .input => Fin 0
  | _, _, .entry n _ rest => Fin (vectorSlots n) ⊕ LayerRole rest
  | _, _, .layer (mid := mid) a _ rest =>
      Fin (vectorSlots a) ⊕ Fin mid ⊕ Fin 1 ⊕ Fin 1 ⊕ LayerRole rest

def fiveSumEquiv (a b c d e : ℕ) :
    (Fin a ⊕ Fin b ⊕ Fin c ⊕ Fin d ⊕ Fin e) ≃ Fin (a+b+c+d+e) :=
  ((Equiv.refl (Fin a)).sumCongr ((Equiv.refl (Fin b)).sumCongr
    ((Equiv.refl (Fin c)).sumCongr finSumFinEquiv))).trans
  (((Equiv.refl (Fin a)).sumCongr ((Equiv.refl (Fin b)).sumCongr finSumFinEquiv)).trans
  (((Equiv.refl (Fin a)).sumCongr finSumFinEquiv).trans
  (finSumFinEquiv.trans (finCongr (by omega)))))

def layerRoleEquiv : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    LayerRole circuit ≃ Fin (layerSlots circuit)
  | _, _, .input => Equiv.refl _
  | _, _, .entry n _ rest =>
      ((Equiv.refl (Fin (vectorSlots n))).sumCongr (layerRoleEquiv rest)).trans finSumFinEquiv
  | _, _, .layer (mid := mid) a _ rest =>
      ((Equiv.refl (Fin (vectorSlots a))).sumCongr
        ((Equiv.refl (Fin mid)).sumCongr
          ((Equiv.refl (Fin 1)).sumCongr
            ((Equiv.refl (Fin 1)).sumCongr (layerRoleEquiv rest))))).trans
        ((fiveSumEquiv (vectorSlots a) mid 1 1 (layerSlots rest)).trans
          (finCongr (by simp only [layerSlots])))

def layerSlot {out input : ℕ} (circuit : Layered.Circuit F out input) (role : LayerRole circuit) : ℕ :=
  (layerRoleEquiv circuit role).val

theorem layerSlot_entry {out next input n : ℕ}
    (e : Entry (SumcheckV2.Cube out) (SumcheckV2.Cube next) n) (rest : Layered.Circuit F next input)
    (i : Fin (vectorSlots n)) :
    layerSlot (.entry n e rest) (.inl i) = i.val := rfl

theorem layerSlot_after_entry {out next input n : ℕ}
    (e : Entry (SumcheckV2.Cube out) (SumcheckV2.Cube next) n) (rest : Layered.Circuit F next input)
    (role : LayerRole rest) :
    layerSlot (.entry n e rest) (.inr role) = vectorSlots n + layerSlot rest role := rfl

theorem layerSlot_assertions {out mid input a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Layered.Circuit F mid input)
    (i : Fin (vectorSlots a)) :
    layerSlot (.layer a body rest) (.inl i) = i.val := rfl

theorem layerSlot_round {out mid input a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Layered.Circuit F mid input)
    (i : Fin mid) :
    layerSlot (.layer a body rest) (.inr (.inl i)) = vectorSlots a + i.val := rfl

theorem layerSlot_terminal {out mid input a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Layered.Circuit F mid input)
    (i : Fin 1) :
    layerSlot (.layer a body rest) (.inr (.inr (.inl i))) = vectorSlots a + mid := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change vectorSlots a + (mid + 0) = _
  omega

theorem layerSlot_combine {out mid input a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Layered.Circuit F mid input)
    (i : Fin 1) :
    layerSlot (.layer a body rest) (.inr (.inr (.inr (.inl i)))) = vectorSlots a + mid + 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change vectorSlots a + (mid + (1 + 0)) = _
  omega

theorem layerSlot_there {out mid input a : ℕ}
    (body : Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F) (rest : Layered.Circuit F mid input)
    (role : LayerRole rest) :
    layerSlot (.layer a body rest) (.inr (.inr (.inr (.inr role)))) =
      vectorSlots a + mid + 2 + layerSlot rest role := by
  change vectorSlots a + (mid + (1 + (1 + layerSlot rest role))) = _
  omega

def LayerRole.kind : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    LayerRole circuit → Linear.Challenges.Kind
  | _, _, .input, role => Fin.elim0 role
  | _, _, .entry n _ rest, role =>
      match role with
      | .inl _ => .ordinary (.assertions n)
      | .inr role => LayerRole.kind rest role
  | _, _, .layer a _ rest, role =>
      match role with
      | .inl _ => .ordinary (.assertions a)
      | .inr (.inl _) => .ordinary .round
      | .inr (.inr (.inl _)) => .terminal
      | .inr (.inr (.inr (.inl _))) => .ordinary .combine
      | .inr (.inr (.inr (.inr role))) => LayerRole.kind rest role

abbrev Role {out input : ℕ} (circuit : Layered.Circuit F out input) := LayerRole circuit

abbrev roleEquiv {out input : ℕ} (circuit : Layered.Circuit F out input) : Role circuit ≃ Fin (slots circuit) :=
  layerRoleEquiv circuit

abbrev roleKind {out input : ℕ} (circuit : Layered.Circuit F out input) : Role circuit → Linear.Challenges.Kind :=
  LayerRole.kind circuit

inductive Message (F : Type) where
  | empty
  | round (polynomial : RoundPoly F)
  | cross (value : F)
  | claims (left right : F)
  deriving DecidableEq

def Message.equiv (F : Type) : Message F ≃ (Unit ⊕ (F × F) ⊕ F ⊕ (F × F)) where
  toFun
    | .empty => .inl ()
    | .round p => .inr (.inl (p.c0, p.c1))
    | .cross value => .inr (.inr (.inl value))
    | .claims a b => .inr (.inr (.inr (a, b)))
  invFun
    | .inl _ => .empty
    | .inr (.inl p) => .round ⟨p.1, p.2⟩
    | .inr (.inr (.inl value)) => .cross value
    | .inr (.inr (.inr p)) => .claims p.1 p.2
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨⟩ | p | value | p <;> rfl

instance [Fintype F] : Fintype (Message F) :=
  Fintype.ofEquiv (Unit ⊕ (F × F) ⊕ F ⊕ (F × F)) (Message.equiv F).symm

def layerMessage : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    Payload circuit → LayerRole circuit → Message F
  | _, _, .input, _, role => Fin.elim0 role
  | _, _, .entry _ _ rest, payload, role =>
      match role with
      | .inl _ => .empty
      | .inr role => layerMessage rest payload role
  | _, _, .layer _ _ rest, payload, role =>
      match role with
      | .inl _ => .empty
      | .inr (.inl i) => .round (payload.1.rounds i)
      | .inr (.inr (.inl _)) => .cross payload.1.cross
      | .inr (.inr (.inr (.inl _))) => .claims payload.1.claimA payload.1.claimB
      | .inr (.inr (.inr (.inr role))) => layerMessage rest payload.2 role

def message {out input : ℕ} (circuit : Layered.Circuit F out input) (payload : Payload circuit) :
    Role circuit → Message F :=
  layerMessage circuit payload

def messageStream {out input : ℕ} (circuit : Layered.Circuit F out input) (payload : Payload circuit) :
    ℕ → Message F :=
  fun i => if h : i < slots circuit then message circuit payload ((roleEquiv circuit).symm ⟨i,h⟩) else .empty

theorem messageStream_at_role {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) (role : Role circuit) :
    messageStream circuit payload (roleEquiv circuit role).val = message circuit payload role := by
  simp [messageStream, (roleEquiv circuit role).isLt]

end LfzkV2.Layered.Replay
