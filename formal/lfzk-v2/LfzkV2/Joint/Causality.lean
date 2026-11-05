import LfzkV2.Joint.RawReplay

/-! The actual mdoc message order: all statements are fixed before either
backend coin, and both responses are fixed before the shared opening. -/

namespace LfzkV2.Joint.Replay

open RecursivePolygero

variable {F₁ F₂ Key C Public : Type}
variable [Field F₁] [Fintype F₁] [DecidableEq F₁]
variable [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype C]
variable {out₁ input₁ out₂ input₂ : ℕ}
variable {circuit₁ : Native.Circuit F₁ out₁ input₁} {I₁ : Instance F₁}
variable {circuit₂ : Native.Circuit F₂ out₂ input₂} {I₂ : Instance F₂}
variable (S₁ : Linear.Runtime.CompiledSide F₁ C (Context Key C Public) circuit₁ I₁)
variable (S₂ : Linear.Runtime.CompiledSide F₂ C (Side.Frontend S₁) circuit₂ I₂)

theorem messages_response_irrel (front : Frontends S₁ S₂)
    (first second : I₁.layer.Payload × I₂.layer.Payload) (j : ℕ)
    (hj : j ≤ backendStart S₁ S₂+1) :
    messages S₁ S₂ (front,first) j = messages S₁ S₂ (front,second) j := by
  unfold messages
  split_ifs with hzero hone htwo hback hnext
  · rfl
  · apply congrArg Message.first
    exact Side.frontend_response_irrel S₁ front.1.1 first.1 second.1 (j-1)
      (by unfold secondStart at hone; omega)
  · apply congrArg Message.second
    exact Side.frontend_response_irrel S₂ front first.2 second.2 (j-secondStart S₁)
      (by unfold backendStart at htwo; omega)
  · rfl
  · rfl
  · omega

/-- Neither field response is available to either backend challenge. The
first field coin is nevertheless in the prefix of the second field coin. -/
theorem backend_response_irrel (front : Frontends S₁ S₂)
    (first second : I₁.layer.Payload × I₂.layer.Payload) (j : ℕ)
    (hj : j ≤ backendStart S₁ S₂+1) :
    hashInput S₁ S₂ (front,first) j = hashInput S₁ S₂ (front,second) j := by
  have hslot : j < slots S₁ S₂ := by unfold slots; omega
  rw [hashInput, dif_pos hslot, hashInput, dif_pos hslot]
  apply Transcript.at_eq_of_message_prefix
  intro i hi
  exact messages_response_irrel S₁ S₂ front first second i (by change i ≤ j at hi; omega)

/-- Equal first backend points contain equal ordered frontend/packing data.
Later backend roles read that same earlier message through `statementsAt`. -/
theorem statements_fixed (first second : Proof S₁ S₂)
    (heq : hashInput S₁ S₂ first (backendStart S₁ S₂) =
      hashInput S₁ S₂ second (backendStart S₁ S₂)) : first.1 = second.1 := by
  have h := congrArg (statementsAt S₁ S₂) heq
  rw [statementsAt_at _ _ _ _ (by unfold slots; omega) le_rfl,
    statementsAt_at _ _ _ _ (by unfold slots; omega) le_rfl] at h
  exact Option.some.inj h

/-- The shared query binds the ordered pair of field responses together. -/
theorem responses_fixed (first second : Proof S₁ S₂)
    (heq : hashInput S₁ S₂ first (backendStart S₁ S₂+2) =
      hashInput S₁ S₂ second (backendStart S₁ S₂+2)) : first.2 = second.2 := by
  have h := congrArg (current S₁ S₂) heq
  rw [current_opening, current_opening] at h
  exact Prod.ext (Message.responses.inj h).1 (Message.responses.inj h).2

end LfzkV2.Joint.Replay
