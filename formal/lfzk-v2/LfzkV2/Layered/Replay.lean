import LfzkV2.Layered.Circuit
import LfzkV2.Linear.Challenges
import LfzkV2.Replay

/-!
# The linear-terminal message and challenge schedule

Each layer sends its cross coefficient before the terminal scale and its two
masked claims before the combining challenge. The plan fixes all four cells
before commitment. Scalar layers still execute both terminal challenges.
-/

namespace LfzkV2.Layered.Replay

open SumcheckV2

variable {F Pad C : Type} [Field F]

structure LayerPads (Pad : Type) (rounds : ℕ) where
  round : Fin rounds → Pad × Pad
  a : Pad
  b : Pad
  ab : Pad
  d : Pad

structure LayerPayload (F : Type) (rounds : ℕ) where
  rounds : Fin rounds → RoundPoly F
  cross : F
  claimA : F
  claimB : F

abbrev PadPlan : {out input : ℕ} → Layered.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .entry _ _ rest => PadPlan rest
  | _, _, .layer (mid := mid) _ _ rest => LayerPads Pad mid × PadPlan rest

abbrev Payload : {out input : ℕ} → Layered.Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .entry _ _ rest => Payload rest
  | _, _, .layer (mid := mid) _ _ rest => LayerPayload F mid × Payload rest

open LfzkV2.Replay (vectorSlots)

def layerSlots : {out input : ℕ} → Layered.Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .entry n _ rest => vectorSlots n + layerSlots rest
  | _, _, .layer (mid := mid) assertions _ rest => vectorSlots assertions + mid + 2 + layerSlots rest

abbrev slots {out input : ℕ} (circuit : Layered.Circuit F out input) : ℕ :=
  layerSlots circuit

def readFrom (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) :
    {out input : ℕ} → (circuit : Layered.Circuit F out input) →
    PadPlan (Pad := Pad) circuit → Payload circuit → (ℕ → C) → ℕ → Circuit.Messages Pad circuit
  | _, _, .input, _, _, _, _ => ()
  | _, _, .entry n _ rest, plan, payload, answers, start =>
      (decode n (answers start), readFrom decode nonzero rest plan payload answers (start + vectorSlots n))
  | _, _, .layer (mid := mid) a _ rest, plan, payload, answers, start =>
      let firstRound := start + vectorSlots a
      let messages : Linear.LayerMessages Pad F mid a :=
        { roundMessages := payload.1.rounds
          roundPads := plan.1.round
          point i := decode 1 (answers (firstRound + i.val)) 0
          beta := decode a (answers start)
          cross := payload.1.cross
          scale := (nonzero (answers (firstRound + mid))).val
          messageA := payload.1.claimA
          messageB := payload.1.claimB
          padA := plan.1.a
          padB := plan.1.b
          padAB := plan.1.ab
          padD := plan.1.d
          alpha := decode 1 (answers (firstRound + mid + 1)) 0 }
      (messages, readFrom decode nonzero rest plan.2 payload.2 answers (firstRound + mid + 2))

def read (decode : (n : ℕ) → C → Fin n → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C) :
    Circuit.Messages Pad circuit :=
  readFrom decode nonzero circuit plan payload answers 0

theorem constraints_total {out input : ℕ} (circuit : Layered.Circuit F out input)
    (m : Circuit.Messages Pad circuit) (weights : Cube out → F) (claim : PadExpression Pad F) :
    ∃ cs, Linear.buildFrom claim (Circuit.proof circuit m weights) = some cs := by
  induction circuit generalizing claim with
  | input => exact ⟨⟨[], claim⟩, rfl⟩
  | entry n e rest ih => exact ih m.2 (e.weights weights m.1) claim
  | layer a body rest ih =>
      let t := m.1.transcript body weights
      obtain ⟨terminal, hterminal⟩ := LfzkV2.Replay.rounds_total
        (Native.subtractConstant claim t.constant) t.rounds t.challenges (by
          simp [t, Linear.LayerMessages.transcript])
      obtain ⟨tail, htail⟩ := ih m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha) t.nextClaim
      refine ⟨⟨t.row terminal :: tail.layers, tail.inputClaim⟩, ?_⟩
      change (do
        let terminal ← (Native.subtractConstant claim t.constant).rounds t.rounds t.challenges
        let rest ← Linear.buildFrom t.nextClaim _
        pure (⟨t.row terminal :: rest.layers, rest.inputClaim⟩ : Linear.Constraints Pad F)) = _
      rw [hterminal, htail]
      rfl

omit [Field F] in
private theorem decoded_vector_eq (decode : (n : ℕ) → C → Fin n → F)
    (first second : ℕ → C) (n start cut : ℕ)
    (hcut : start + LfzkV2.Replay.vectorSlots n ≤ cut)
    (hanswers : ∀ j, j < cut → first j = second j) :
    decode n (first start) = decode n (second start) := by
  by_cases hn : n = 0
  · subst n
    funext i
    exact Fin.elim0 i
  · have hs : LfzkV2.Replay.vectorSlots n = 1 := by simp [LfzkV2.Replay.vectorSlots, hn]
    rw [hanswers start (by omega)]

theorem readFrom_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit)
    (first second : ℕ → C) (start : ℕ)
    (hanswers : ∀ j, j < start + layerSlots circuit → first j = second j) :
    readFrom decode nonzero circuit plan payload first start =
      readFrom decode nonzero circuit plan payload second start := by
  induction circuit generalizing start with
  | input => rfl
  | @entry out next input n e rest ih =>
      have hb := decoded_vector_eq decode first second n start
        (start + layerSlots (.entry n e rest)) (by simp only [layerSlots]; omega) hanswers
      have hr := ih plan payload (start + vectorSlots n) (by
        intro j hj
        apply hanswers j
        simp only [layerSlots]
        omega)
      dsimp only [readFrom]
      rw [hb, hr]
  | @layer out mid input a body rest ih =>
      have hb := decoded_vector_eq decode first second a start
        (start + layerSlots (Layered.Circuit.layer a body rest))
        (by simp only [layerSlots]; omega) hanswers
      have hp : (fun i : Fin mid => decode 1 (first (start + LfzkV2.Replay.vectorSlots a + i.val)) 0) =
          (fun i : Fin mid => decode 1 (second (start + LfzkV2.Replay.vectorSlots a + i.val)) 0) := by
        funext i
        rw [hanswers _ (by simp only [layerSlots]; omega)]
      have ha := hanswers (start + LfzkV2.Replay.vectorSlots a + mid)
        (by simp only [layerSlots]; omega)
      have ht := hanswers (start + LfzkV2.Replay.vectorSlots a + mid + 1)
        (by simp only [layerSlots]; omega)
      have hr := ih plan.2 payload.2 (start + LfzkV2.Replay.vectorSlots a + mid + 2) (by
        intro j hj
        apply hanswers j
        simp only [layerSlots]
        omega)
      dsimp only [readFrom]
      rw [hb, hp, ha, ht, hr]

theorem read_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit)
    (first second : ℕ → C)
    (hanswers : ∀ j, j < slots circuit → first j = second j) :
    read decode nonzero circuit plan payload first = read decode nonzero circuit plan payload second :=
  readFrom_eq_of_prefix decode nonzero circuit plan payload first second 0
    (by simpa [slots] using hanswers)

structure Reconstruction {out input : ℕ} (circuit : Layered.Circuit F out input) (Pad : Type) where
  messages : Circuit.Messages Pad circuit
  constraints : Linear.Constraints Pad F
  built : Linear.buildConstraints (Circuit.proof circuit messages 0) = some constraints

noncomputable def reconstructionFromAnswers (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit) (answers : ℕ → C) :
    Reconstruction circuit Pad :=
  let m := read decode nonzero circuit plan payload answers
  let h := constraints_total circuit m 0 zeroClaim
  ⟨m, h.choose, h.choose_spec⟩

@[ext] theorem Reconstruction.ext {out input : ℕ} {circuit : Layered.Circuit F out input}
    {first second : Reconstruction circuit Pad}
    (hmessages : first.messages = second.messages)
    (hconstraints : first.constraints = second.constraints) : first = second := by
  cases first
  cases second
  cases hmessages
  cases hconstraints
  rfl

theorem reconstructionFromAnswers_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : PadPlan (Pad := Pad) circuit) (payload : Payload circuit)
    (first second : ℕ → C)
    (hanswers : ∀ j, j < slots circuit → first j = second j) :
    reconstructionFromAnswers decode nonzero circuit plan payload first =
      reconstructionFromAnswers decode nonzero circuit plan payload second := by
  have hm := read_eq_of_prefix decode nonzero circuit plan payload first second hanswers
  apply Reconstruction.ext hm
  apply Option.some.inj
  rw [← (reconstructionFromAnswers decode nonzero circuit plan payload first).built,
    ← (reconstructionFromAnswers decode nonzero circuit plan payload second).built]
  exact congrArg Linear.buildConstraints (by
    dsimp only [reconstructionFromAnswers]
    rw [hm])

end LfzkV2.Layered.Replay
