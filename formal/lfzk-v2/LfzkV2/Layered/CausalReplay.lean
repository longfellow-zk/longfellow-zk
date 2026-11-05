import LfzkV2.Layered.SemanticReplay

/-! Causality of the actual linear-terminal replay. The terminal polynomial
cannot read its scale or either subsequent masked claim. The combining test
may read both, but cannot read its own combining challenge. -/

namespace LfzkV2.Layered.Replay

open SumcheckV2 Linear.Challenges
open LfzkV2.Replay (vectorSlots)

variable {F Pad C : Type} [Field F]

omit [Field F] in
private theorem vector_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (first second : ℕ → C) (n start cut : ℕ)
    (hcut : start + vectorSlots n ≤ cut)
    (hanswers : ∀ j, j < cut → first j = second j) :
    decode n (first start) = decode n (second start) := by
  by_cases hn : n = 0
  · subst n
    funext i
    exact Fin.elim0 i
  · have hs : vectorSlots n = 1 := by simp [vectorSlots, hn]
    rw [hanswers start (by omega)]

theorem layerData_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (firstPayload secondPayload : Payload circuit)
    (first second : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (role : LayerRole circuit)
    (hanswers : ∀ j, j < start + layerSlot circuit role → first j = second j)
    (hmessages : ∀ earlier, layerSlot circuit earlier ≤ layerSlot circuit role →
      layerMessage circuit firstPayload earlier = layerMessage circuit secondPayload earlier) :
    layerData decode nonzero circuit plan firstPayload first start w weights pads claim role =
      layerData decode nonzero circuit plan secondPayload second start w weights pads claim role := by
  induction circuit generalizing start claim with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => rfl
      | inr role =>
          have hb := vector_eq_of_prefix decode first second n start
            (start + layerSlot (.entry n e rest) (.inr role))
            (by simp only [layerSlot_after_entry]; omega) hanswers
          dsimp only [layerData, LayerRole.kind]
          rw [hb]
          apply ih
          · intro j hj
            exact hanswers j (by simp only [layerSlot_after_entry]; omega)
          · intro earlier he
            exact hmessages (.inr earlier) (by simp only [layerSlot_after_entry]; omega)
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | i | role
      · rfl
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (.layer a body rest) (.inr (.inl i)))
          (by simp only [layerSlot_round]; omega) hanswers
        have hp : SumcheckV1.extract_prefix
            (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) i =
            SumcheckV1.extract_prefix
              (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) i := by
          funext j
          change decode 1 (first (start + vectorSlots a + j.val)) 0 =
            decode 1 (second (start + vectorSlots a + j.val)) 0
          rw [hanswers _ (by simp only [layerSlot_round]; have hj := j.isLt; omega)]
        dsimp only [layerData, LayerRole.kind, readFrom]
        rw [hb, hp]
        apply RoundReplay.dataAt_eq_of_message_prefix
        intro j hj
        have hm := hmessages (.inr (.inl j)) (by
          simp only [layerSlot_round]
          exact Nat.add_le_add_left hj _)
        have hpoly := Message.round.inj hm
        simp only [clearMessages, hpoly]
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (.layer a body rest) (.inr (.inr (.inl i))))
          (by simp only [layerSlot_terminal]; omega) hanswers
        have hp : (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) =
            (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [layerSlot_terminal]; have hj := j.isLt; omega)]
        have hr : firstPayload.1.rounds = secondPayload.1.rounds := by
          funext j
          apply Message.round.inj
          exact hmessages (.inr (.inl j)) (by
            simp only [layerSlot_round, layerSlot_terminal]
            have hj := j.isLt
            omega)
        have hc := Message.cross.inj (hmessages (.inr (.inr (.inl i))) (le_refl _))
        dsimp only [layerData, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.finalClaim, Linear.LayerTranscript.clearRounds, Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hr, hc]
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (.layer a body rest) (.inr (.inr (.inr (.inl i)))))
          (by simp only [layerSlot_combine]; omega) hanswers
        have hp : (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) =
            (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [layerSlot_combine]; have hj := j.isLt; omega)]
        have hs : nonzero (first (start + vectorSlots a + mid)) =
            nonzero (second (start + vectorSlots a + mid)) := by
          rw [hanswers _ (by simp only [layerSlot_combine]; omega)]
        have hc := Message.claims.inj (hmessages (.inr (.inr (.inr (.inl i)))) (le_refl _))
        dsimp only [layerData, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.clearA, Linear.LayerTranscript.clearB, Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hs, hc.1, hc.2]
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (.layer a body rest) (.inr (.inr (.inr (.inr role)))))
          (by simp only [layerSlot_there]; omega) hanswers
        have hp : (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) =
            (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [layerSlot_there]; have hj := j.isLt; omega)]
        have hs : nonzero (first (start + vectorSlots a + mid)) =
            nonzero (second (start + vectorSlots a + mid)) := by
          rw [hanswers _ (by simp only [layerSlot_there]; omega)]
        have ha : decode 1 (first (start + vectorSlots a + mid + 1)) 0 =
            decode 1 (second (start + vectorSlots a + mid + 1)) 0 := by
          rw [hanswers _ (by simp only [layerSlot_there]; omega)]
        have hc := Message.claims.inj (hmessages (.inr (.inr (.inr (.inl 0)))) (by
          simp only [layerSlot_combine, layerSlot_there]
          omega))
        have htail : ∀ j, j < start + vectorSlots a + mid + 2 + layerSlot rest role →
            first j = second j := by
          intro j hj
          exact hanswers j (by simp only [layerSlot_there]; omega)
        have hmsg : ∀ earlier, layerSlot rest earlier ≤ layerSlot rest role →
            layerMessage rest firstPayload.2 earlier = layerMessage rest secondPayload.2 earlier := by
          intro earlier he
          exact hmessages (.inr (.inr (.inr (.inr earlier)))) (by simp only [layerSlot_there]; omega)
        dsimp only [layerData, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.nextValue, Linear.LayerTranscript.clearA, Linear.LayerTranscript.clearB,
          Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hs, ha, hc.1, hc.2]
        exact ih _ _ _ _ _ _ _ _ htail hmsg

theorem semanticData_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (firstPayload secondPayload : Payload circuit)
    (first second : ℕ → C) (w : Cube input → F) (pads : Pad → F) (role : Role circuit)
    (hanswers : ∀ j, j < (roleEquiv circuit role).val → first j = second j)
    (hmessages : ∀ earlier, (roleEquiv circuit earlier).val ≤ (roleEquiv circuit role).val →
      message circuit firstPayload earlier = message circuit secondPayload earlier) :
    semanticData decode nonzero circuit plan firstPayload first w pads role =
      semanticData decode nonzero circuit plan secondPayload second w pads role := by
  apply layerData_eq_of_prefix
  · simpa only [Nat.zero_add, layerSlot] using hanswers
  · exact hmessages

end LfzkV2.Layered.Replay
