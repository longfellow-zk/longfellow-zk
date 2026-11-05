import LfzkV2.Layered.Schedule

/-! Reconstruct just the message prefix needed by each challenge test. -/

namespace LfzkV2.Layered.Replay

open SumcheckV2
open LfzkV2.Replay (vectorSlots)

variable {F : Type} [Zero F]

def Message.asRound : Message F → RoundPoly F
  | .round p => p
  | _ => ⟨0, 0⟩

def Message.asCross : Message F → F
  | .cross value => value
  | _ => 0

def Message.asClaims : Message F → F × F
  | .claims a b => (a, b)
  | _ => (0, 0)

def parseLayer : {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    (ℕ → Message F) → Payload circuit
  | _, _, .input, _ => ()
  | _, _, .entry n _ rest, stream => parseLayer rest (fun j => stream (vectorSlots n+j))
  | _, _, .layer (mid := mid) a _ rest, stream =>
      (⟨fun i => (stream (vectorSlots a+i.val)).asRound,
        (stream (vectorSlots a+mid)).asCross,
        (stream (vectorSlots a+mid+1)).asClaims.1,
        (stream (vectorSlots a+mid+1)).asClaims.2⟩,
        parseLayer rest (fun j => stream (vectorSlots a+mid+2+j)))

theorem layerMessage_parse_eq {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) (stream : ℕ → Message F) (role : LayerRole circuit)
    (hstream : ∀ earlier, layerSlot circuit earlier ≤ layerSlot circuit role →
      stream (layerSlot circuit earlier) = layerMessage circuit payload earlier) :
    layerMessage circuit (parseLayer circuit stream) role = layerMessage circuit payload role := by
  induction circuit generalizing stream with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => rfl
      | inr role =>
          apply ih
          intro earlier he
          exact hstream (.inr earlier) (by simp only [layerSlot_after_entry]; omega)
  | layer a body rest ih =>
      rcases role with i | i | i | i | role
      · rfl
      · have hs := hstream (.inr (.inl i)) (le_refl _)
        simp only [layerSlot_round, layerMessage] at hs
        dsimp only [layerMessage, parseLayer]
        rw [hs]
        rfl
      · have hs := hstream (.inr (.inr (.inl i))) (le_refl _)
        simp only [layerSlot_terminal, layerMessage] at hs
        dsimp only [layerMessage, parseLayer]
        rw [hs]
        rfl
      · have hs := hstream (.inr (.inr (.inr (.inl i)))) (le_refl _)
        simp only [layerSlot_combine, layerMessage] at hs
        dsimp only [layerMessage, parseLayer]
        rw [hs]
        rfl
      · apply ih
        intro earlier he
        have hs := hstream (.inr (.inr (.inr (.inr earlier)))) (by
          rw [layerSlot_there, layerSlot_there]
          omega)
        simpa only [layerSlot_there, layerMessage] using hs

def parsePayload {out input : ℕ} (circuit : Layered.Circuit F out input)
    (stream : ℕ → Message F) : Payload circuit :=
  parseLayer circuit stream

theorem message_parse_eq {out input : ℕ} (circuit : Layered.Circuit F out input)
    (payload : Payload circuit) (stream : ℕ → Message F) (role : Role circuit)
    (hstream : ∀ earlier, (roleEquiv circuit earlier).val ≤ (roleEquiv circuit role).val →
      stream (roleEquiv circuit earlier).val = message circuit payload earlier) :
    message circuit (parsePayload circuit stream) role = message circuit payload role := by
  exact layerMessage_parse_eq circuit payload stream role hstream

end LfzkV2.Layered.Replay
