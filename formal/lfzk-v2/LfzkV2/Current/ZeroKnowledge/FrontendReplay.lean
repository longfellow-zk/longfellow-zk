import LfzkV2.Current.ZeroKnowledge.FrontendCorrectness

/-! A pointwise bridge to the current verifier's grouped answer replay.
The abstract stateful reader may carry an adaptive oracle and transcript
prefix; here an already fixed answer tape recovers the exact public compiler
input used by `Current.FrontendReplay`. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F C Pad : Type} [Field F]

def answerReader (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (answers : ℕ → C) : CircuitReader F ℕ where
  round state _ := (decode (answers state) 0,state+1)
  terminal state _ := (nonzero (answers state),state+1)
  combine state _ := (decode (answers state) 0,state+1)
  assertions state count := (fun i : Fin count => decode (answers state) i.val,state+1)
  inputAssertions state count := (fun i : Fin count => decode (answers (state-1)) (1+i.val),state)

theorem readRounds_answers (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (answers : ℕ → C) {n : ℕ} (state : ℕ) (messages : Fin n → RoundPoly F) :
    readRounds (answerReader decode nonzero answers).toReader state messages =
      (fun i : Fin n => decode (answers (state+i.val)) 0,state+n) := by
  induction n generalizing state with
  | zero =>
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · simp only [readRounds,Nat.add_zero]
  | succ n ih =>
      simp only [readRounds]
      rw [ih]
      apply Prod.ext
      · funext i
        cases i using Fin.cases with
        | zero => simp [answerReader]
        | succ i => simp [answerReader,Nat.add_assoc,Nat.add_comm 1 i.val]
      · simp [answerReader,Nat.add_assoc,Nat.add_comm 1 n]

theorem readLayer_answers (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (answers : ℕ → C) {n : ℕ} (state : ℕ) (payload : LayerPayload F n) :
    readLayer (answerReader decode nonzero answers).toReader state payload =
      ⟨fun i => decode (answers (state+i.val)) 0,nonzero (answers (state+n)),
        decode (answers (state+n+1)) 0,state+n+2⟩ := by
  unfold readLayer
  rw [readRounds_answers]
  rfl

def replayStart {out input : ℕ} (_circuit : Layered.Circuit F out input)
    (state : ℕ) (continuing : Bool) : ℕ :=
  if continuing then state-1 else state

def replayOffset {out input : ℕ} (_circuit : Layered.Circuit F out input)
    (continuing : Bool) : ℕ :=
  if continuing then 1 else 0

theorem readSetup_answers (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (answers : ℕ → C) {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (state : ℕ) (continuing : Bool)
    (hstate : continuing = true → 0 < state) :
    messagesFromSetup circuit
        (readSetup (answerReader decode nonzero answers) plan ids payload state continuing).1 payload =
      FrontendReplay.readFrom decode nonzero circuit ids payload answers
        (replayStart circuit state continuing) (replayOffset circuit continuing) := by
  induction plan generalizing state continuing with
  | input => rfl
  | inputEntry =>
      cases continuing <;> simp [readSetup,messagesFromSetup,inputCoefficients,answerReader,
        replayStart,replayOffset,FrontendReplay.readFrom]
  | @layer out mid input assertions body rest metadata tail ih =>
      obtain ⟨start, hstart, hnext⟩ : ∃ start, replayStart (.layer assertions body rest) state continuing = start ∧
          (inputCoefficients (answerReader decode nonzero answers) continuing state assertions).2 = start+1 := by
        cases continuing
        · exact ⟨state, rfl, rfl⟩
        · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt (hstate rfl)
          exact ⟨s, by simp [replayStart], by simp [inputCoefficients, answerReader]⟩
      dsimp only [readSetup,messagesFromSetup,setupLayer]
      rw [readLayer_answers, hstart, hnext]
      apply Prod.ext
      · have hbeta : (inputCoefficients (answerReader decode nonzero answers) continuing state assertions).1 =
            fun i => decode (answers start) (replayOffset (.layer assertions body rest) continuing+i.val) := by
          cases continuing
          · simp only [replayStart] at hstart
            subst hstart
            simp [inputCoefficients, answerReader, replayOffset]
          · simp only [replayStart] at hstart
            subst hstart
            simp [inputCoefficients, answerReader, replayOffset]
        simp [FrontendReplay.readFrom, hbeta, linearPlan, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      · have h := ih ids.2 payload.2 (start+1+mid+2) true (fun _ => by omega)
        simpa [replayStart,replayOffset,FrontendReplay.readFrom,
          answerReader,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
  | @entryLayer out next mid input checks assertions entries entry body rest metadata tail ih =>
      obtain ⟨start, hstart, hnext⟩ : ∃ start, replayStart (.entry checks entry (.layer assertions body rest)) state continuing = start ∧
          (inputCoefficients (answerReader decode nonzero answers) continuing state (checks+assertions)).2 = start+1 := by
        cases continuing
        · exact ⟨state, rfl, rfl⟩
        · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_lt (hstate rfl)
          exact ⟨s, by simp [replayStart], by simp [inputCoefficients, answerReader]⟩
      have hcoeff : (inputCoefficients (answerReader decode nonzero answers) continuing state (checks+assertions)).1 =
          fun i => decode (answers start) (replayOffset (.entry checks entry (.layer assertions body rest)) continuing+i.val) := by
        cases continuing
        · simp only [replayStart] at hstart
          subst hstart
          simp [inputCoefficients, answerReader, replayOffset]
        · simp only [replayStart] at hstart
          subst hstart
          simp [inputCoefficients, answerReader, replayOffset]
      dsimp only [readSetup,messagesFromSetup,setupLayer]
      rw [readLayer_answers, hstart, hnext, hcoeff]
      apply Prod.ext
      · simp [FrontendReplay.readFrom, replayOffset]
      · apply Prod.ext
        · simp [FrontendReplay.readFrom, replayOffset, linearPlan, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        · have h := ih ids.2 payload.2 (start+1+mid+2) true (fun _ => by omega)
          simpa [replayStart,replayOffset,FrontendReplay.readFrom,
            answerReader,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem readSetup_answers_initial (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    (answers : ℕ → C) {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) :
    messagesFromSetup circuit
        (readSetup (answerReader decode nonzero answers) plan ids payload 0 false).1 payload =
      FrontendReplay.read decode nonzero circuit ids payload answers := by
  simpa only [replayStart,replayOffset,Bool.false_eq_true,↓reduceIte,
    FrontendReplay.read] using readSetup_answers decode nonzero answers plan ids payload 0 false
      (fun h => Bool.false_ne_true h |>.elim)

/-- The public simulator's payload reconstructs through the current verifier
reader, and its recovered cells satisfy that reader's actual affine rows. -/
theorem simulated_current_constraints
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (answers : ℕ → C)
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (w : Cube input → F) (hvalid : circuit.Satisfies w)
    (payload : Layered.Replay.Payload circuit) :
    let ids := CellLayout.Pads.plan circuit id
    let messages := FrontendReplay.read decode nonzero circuit ids payload answers
    let pads := recoveredPadValues (answerReader decode nonzero answers) plan w 0 0 payload
    ∃ cs, Linear.buildConstraints (circuit.proof messages 0) = some cs ∧
      cs.Holds pads (dot (circuit.inputWeights messages 0) w) := by
  have h := simulated_constraints (answerReader decode nonzero answers) plan w hvalid 0 payload
  dsimp only at h ⊢
  rw [readSetup_answers_initial] at h
  exact h

end LfzkV2.Current.ZeroKnowledge.Frontend
