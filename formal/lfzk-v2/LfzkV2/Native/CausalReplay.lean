import LfzkV2.Native.SemanticReplay

/-! Exact V2 tests depend only on prior challenge blocks and the messages
through their own role. In particular, the assertion test does not read its
own answer, and a round test ignores later messages as well as later coins. -/

namespace LfzkV2.Native.Replay

open SumcheckV2 ChallengeBlocks LfzkV2.Replay

variable {F Pad Slot C : Type} [Field F]

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
  · have hs : vectorSlots n = 1 := by simp [vectorSlots,hn]
    rw [hanswers start (by omega)]

theorem layerData_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (firstPayload secondPayload : Payload circuit)
    (first second : ℕ → C) (start : ℕ) (w : Cube input → F) (weights : Cube out → F)
    (pads : Pad → F) (claim : F) (role : LayerRole circuit.shape)
    (hanswers : ∀ j, j < start + layerSlot circuit.shape role → first j = second j)
    (hmessages : ∀ earlier, layerSlot circuit.shape earlier ≤ layerSlot circuit.shape role →
      layerMessage circuit.shape firstPayload earlier = layerMessage circuit.shape secondPayload earlier) :
    layerData decode circuit plan firstPayload first start w weights pads claim role =
      layerData decode circuit plan secondPayload second start w weights pads claim role := by
  induction circuit generalizing start claim with
  | input => exact Fin.elim0 role
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | role
      · rfl
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (Circuit.layer a body rest).shape (.inr (.inl i)))
          (by simp only [Circuit.shape, layerSlot_round]; omega) hanswers
        have hp : SumcheckV1.extract_prefix
            (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) i =
            SumcheckV1.extract_prefix
              (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) i := by
          funext j
          change decode 1 (first (start + vectorSlots a + j.val)) 0 =
            decode 1 (second (start + vectorSlots a + j.val)) 0
          rw [hanswers _ (by simp only [Circuit.shape, layerSlot_round]; have hj := j.isLt; omega)]
        dsimp only [layerData, Circuit.shape, LayerRole.kind, readFrom]
        rw [hb,hp]
        apply RoundReplay.dataAt_eq_of_message_prefix
        intro j hj
        have hm := hmessages (.inr (.inl j)) (by
          simp only [Circuit.shape, layerSlot_round]
          exact Nat.add_le_add_left hj _)
        have hpoly := Message.round.inj hm
        simp only [clearMessages,hpoly]
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (Circuit.layer a body rest).shape (.inr (.inr (.inl i))))
          (by simp only [Circuit.shape, layerSlot_combine]; omega) hanswers
        have hp : (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) =
            (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [Circuit.shape, layerSlot_combine]; have hj := j.isLt; omega)]
        have hc := Message.claims.inj (hmessages (.inr (.inr (.inl i))) (le_refl _))
        dsimp only [layerData, Circuit.shape, LayerRole.kind, readFrom, CircuitLayer.transcript,
          LayerTranscript.nextValue, LfzkV2.LayerMessages.transcript,
          LfzkV2.LayerTranscript.clearA, LfzkV2.LayerTranscript.clearB]
        rw [hb,hp,hc.1,hc.2]
      · have hb := vector_eq_of_prefix decode first second a start
          (start + layerSlot (Circuit.layer a body rest).shape (.inr (.inr (.inr role))))
          (by simp only [Circuit.shape, layerSlot_there]; omega) hanswers
        have hp : (fun j : Fin mid => decode 1 (first (start + vectorSlots a + j.val)) 0) =
            (fun j : Fin mid => decode 1 (second (start + vectorSlots a + j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [Circuit.shape, layerSlot_there]; have hj := j.isLt; omega)]
        have ha : decode 1 (first (start + vectorSlots a + mid)) 0 =
            decode 1 (second (start + vectorSlots a + mid)) 0 := by
          rw [hanswers _ (by simp only [Circuit.shape, layerSlot_there]; omega)]
        have hc := Message.claims.inj (hmessages (.inr (.inr (.inl 0))) (by
          simp only [Circuit.shape, layerSlot_combine,layerSlot_there]
          omega))
        have htail : ∀ j, j < start + vectorSlots a + mid + 1 + layerSlot rest.shape role → first j = second j := by
          intro j hj
          exact hanswers j (by simp only [Circuit.shape, layerSlot_there]; omega)
        have hmsg : ∀ earlier, layerSlot rest.shape earlier ≤ layerSlot rest.shape role →
            layerMessage rest.shape firstPayload.2 earlier = layerMessage rest.shape secondPayload.2 earlier := by
          intro earlier he
          exact hmessages (.inr (.inr (.inr earlier))) (by simp only [Circuit.shape, layerSlot_there]; omega)
        dsimp only [layerData, Circuit.shape, LayerRole.kind, readFrom, CircuitLayer.transcript,
          LayerTranscript.nextValue, LfzkV2.LayerMessages.transcript,
          LfzkV2.LayerTranscript.clearA, LfzkV2.LayerTranscript.clearB]
        rw [hb,hp,ha,hc.1,hc.2]
        apply ih
        · exact htail
        · exact hmsg

theorem semanticData_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (firstPayload secondPayload : Payload circuit)
    (first second : ℕ → C) (w : Cube input → F) (pads : Pad → F) (role : Role circuit.shape)
    (hanswers : ∀ j, j < (roleEquiv circuit.shape role).val → first j = second j)
    (hmessages : ∀ earlier, (roleEquiv circuit.shape earlier).val ≤ (roleEquiv circuit.shape role).val →
      message circuit.shape firstPayload earlier = message circuit.shape secondPayload earlier) :
    semanticData decode circuit plan firstPayload first w pads role =
      semanticData decode circuit plan secondPayload second w pads role := by
  cases role with
  | inl _ => rfl
  | inr role =>
      have hp : outputPoint decode out first = outputPoint decode out second := by
        by_cases ho : out = 0
        · subst out
          funext i
          exact Fin.elim0 i
        · have hs : vectorSlots out = 1 := by simp [vectorSlots,ho]
          have hzero : 0 < (roleEquiv circuit.shape (.inr role)).val := by
            change 0 < vectorSlots out + layerSlot circuit.shape role
            omega
          unfold outputPoint
          rw [hanswers 0 hzero]
      dsimp only [semanticData]
      rw [hp]
      apply layerData_eq_of_prefix
      · exact hanswers
      · intro earlier he
        exact hmessages (.inr earlier) (by
          change vectorSlots out + layerSlot circuit.shape earlier ≤ vectorSlots out + layerSlot circuit.shape role
          omega)

end LfzkV2.Native.Replay
