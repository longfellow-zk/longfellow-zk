import LfzkV2.Current.FrontendFailures
import LfzkV2.Current.QueryAnswers

/-! Grouped local tests cannot inspect future answers or messages. A test may
use coordinates of its own answer: entry coefficients and assertion
coefficients share that answer. Later counting treats the complete answer as
one argument and proves its full-block bound, rather than incorrectly assuming
that every intermediate algebraic datum is independent of that whole answer. -/
namespace LfzkV2.Current.FrontendReplay
open SumcheckV2 Linear.Challenges
open Layered.Replay (LayerRole layerMessage Message clearMessages)

variable {F Pad C : Type} [Field F]

theorem sampleAtRole_eq_of_current (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input) (role : LayerRole circuit)
    (first second : ℕ → C) (start offset : ℕ)
    (h : first (queryIndex circuit role start) = second (queryIndex circuit role start)) :
    sampleAtRole decode nonzero circuit role first start offset =
      sampleAtRole decode nonzero circuit role second start offset := by
  induction circuit generalizing start offset with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ =>
          simp only [queryIndex] at h
          dsimp only [sampleAtRole, LayerRole.kind]
          rw [h]
      | inr role => exact ih role start (offset+n) h
  | layer a body rest ih =>
      rcases role with i | i | i | i | role
      · simp only [queryIndex] at h
        dsimp only [sampleAtRole, LayerRole.kind]
        rw [h]
      · simp only [queryIndex] at h
        dsimp only [sampleAtRole, LayerRole.kind]
        rw [h]
      · simp only [queryIndex] at h
        dsimp only [sampleAtRole, LayerRole.kind]
        rw [h]
      · simp only [queryIndex] at h
        dsimp only [sampleAtRole, LayerRole.kind]
        rw [h]
      · exact ih role _ _ h

theorem dataAtRole_eq_of_inclusive_prefix (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (firstPayload secondPayload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (role : LayerRole circuit)
    (hanswers : ∀ j, j ≤ queryIndex circuit role start → first j = second j)
    (hmessages : ∀ earlier,
      queryIndex circuit earlier start ≤ queryIndex circuit role start →
      layerMessage circuit firstPayload earlier = layerMessage circuit secondPayload earlier) :
    dataAtRole decode nonzero circuit plan firstPayload first start offset w weights pads claim role =
      dataAtRole decode nonzero circuit plan secondPayload second start offset w weights pads claim role := by
  induction circuit generalizing start offset claim with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ => rfl
      | inr role =>
          have hs := hanswers start (queryIndex_ge rest role start)
          dsimp only [dataAtRole, LayerRole.kind]
          rw [hs]
          apply ih
          · exact hanswers
          · intro earlier he
            exact hmessages (.inr earlier) he
  | @layer out mid input a body rest ih =>
      rcases role with i | i | i | i | role
      · rfl
      · have hb := hanswers start (by simp only [queryIndex]; omega)
        have hp : SumcheckV1.extract_prefix
            (fun j : Fin mid => decode (first (start+1+j.val)) 0) i =
            SumcheckV1.extract_prefix
              (fun j : Fin mid => decode (second (start+1+j.val)) 0) i := by
          funext j
          change decode (first (start+1+j.val)) 0 = decode (second (start+1+j.val)) 0
          rw [hanswers _ (by simp only [queryIndex]; have hj := j.isLt; omega)]
        dsimp only [dataAtRole, LayerRole.kind, readFrom]
        rw [hb, hp]
        apply RoundReplay.dataAt_eq_of_message_prefix
        intro j hj
        have hm := hmessages (.inr (.inl j)) (by simp only [queryIndex]; omega)
        have hpoly := Message.round.inj hm
        simp only [clearMessages, hpoly]
      · have hb := hanswers start (by simp only [queryIndex]; omega)
        have hp : (fun j : Fin mid => decode (first (start+1+j.val)) 0) =
            (fun j : Fin mid => decode (second (start+1+j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [queryIndex]; have hj := j.isLt; omega)]
        have hr : firstPayload.1.rounds = secondPayload.1.rounds := by
          funext j
          apply Message.round.inj
          exact hmessages (.inr (.inl j)) (by simp only [queryIndex]; have hj := j.isLt; omega)
        have hc := Message.cross.inj
          (hmessages (.inr (.inr (.inl i))) (le_refl _))
        dsimp only [dataAtRole, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.finalClaim, Linear.LayerTranscript.clearRounds,
          Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hr, hc]
      · have hb := hanswers start (by simp only [queryIndex]; omega)
        have hp : (fun j : Fin mid => decode (first (start+1+j.val)) 0) =
            (fun j : Fin mid => decode (second (start+1+j.val)) 0) := by
          funext j
          rw [hanswers _ (by simp only [queryIndex]; have hj := j.isLt; omega)]
        have hs : nonzero (first (start+1+mid)) = nonzero (second (start+1+mid)) := by
          rw [hanswers _ (by simp only [queryIndex]; omega)]
        have hc := Message.claims.inj
          (hmessages (.inr (.inr (.inr (.inl i)))) (le_refl _))
        dsimp only [dataAtRole, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.clearA, Linear.LayerTranscript.clearB,
          Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hs, hc.1, hc.2]
      · let next := if hasLayers rest then start+mid+3 else start+mid+2
        have hnext : start+mid+2 ≤ queryIndex rest role next := by
          have h := queryIndex_ge rest role next
          dsimp [next] at h ⊢
          split_ifs at h ⊢ <;> omega
        have hb := hanswers start (by change _ ≤ queryIndex rest role next; omega)
        have hp : (fun j : Fin mid => decode (first (start+1+j.val)) 0) =
            (fun j : Fin mid => decode (second (start+1+j.val)) 0) := by
          funext j
          rw [hanswers _ (by change _ ≤ queryIndex rest role next; have hj := j.isLt; omega)]
        have hs : nonzero (first (start+1+mid)) = nonzero (second (start+1+mid)) := by
          rw [hanswers _ (by change _ ≤ queryIndex rest role next; omega)]
        have ha : decode (first (start+mid+2)) 0 = decode (second (start+mid+2)) 0 := by
          rw [hanswers _ hnext]
        have hc := Message.claims.inj
          (hmessages (.inr (.inr (.inr (.inl 0)))) hnext)
        have htail : ∀ j, j ≤ queryIndex rest role next → first j = second j := hanswers
        have hmsg : ∀ earlier, queryIndex rest earlier next ≤ queryIndex rest role next →
            layerMessage rest firstPayload.2 earlier = layerMessage rest secondPayload.2 earlier := by
          intro earlier he
          exact hmessages (.inr (.inr (.inr (.inr earlier)))) he
        dsimp only [dataAtRole, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
          Linear.LayerTranscript.nextValue, Linear.LayerTranscript.clearA,
          Linear.LayerTranscript.clearB, Linear.LayerTranscript.terminalPads]
        rw [hb, hp, hs, ha, hc.1, hc.2]
        exact ih _ _ _ _ _ _ _ _ _ htail hmsg

/-- The whole grouped failure predicate depends on the prefix through its own
query, including that query's candidate answer, and no later messages. -/
theorem badAt_eq_of_inclusive_prefix (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (firstPayload secondPayload : Layered.Replay.Payload circuit)
    (first second : ℕ → C) (w : Cube input → F) (pads : Pad → F) (query : ℕ)
    (hanswers : ∀ j, j ≤ query → first j = second j)
    (hmessages : ∀ role, queryIndex circuit role 0 ≤ query →
      layerMessage circuit firstPayload role = layerMessage circuit secondPayload role) :
    BadAt decode nonzero circuit plan firstPayload first w pads query ↔
      BadAt decode nonzero circuit plan secondPayload second w pads query := by
  unfold BadAt
  apply exists_congr
  intro role
  by_cases hi : queryIndex circuit role 0 = query
  · have hd := dataAtRole_eq_of_inclusive_prefix decode nonzero circuit plan
      firstPayload secondPayload first second 0 0 w 0 pads 0 role
      (fun j hj => hanswers j (by simpa only [hi] using hj))
      (fun earlier he => hmessages earlier (by simpa only [hi] using he))
    have hs := sampleAtRole_eq_of_current decode nonzero circuit role first second 0 0
      (by rw [hi]; exact hanswers query (le_refl _))
    rw [hd, hs]
  · simp only [hi, false_and]

/-- Freezing future answers loses no failing test. The current answer is
passed explicitly, making this predicate suitable for one-query counting. -/
theorem badAt_from_prefix (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (fallback : C) (w : Cube input → F) (pads : Pad → F) (query : ℕ) :
    BadAt decode nonzero circuit plan payload answers w pads query ↔
      BadAt decode nonzero circuit plan payload
        (completeAnswers (fun i : Fin query => answers i.val) (answers query) fallback) w pads query := by
  apply badAt_eq_of_inclusive_prefix
  · intro j hj
    exact (completeAnswers_agrees answers query fallback j hj).symm
  · intro role _
    rfl

end LfzkV2.Current.FrontendReplay
