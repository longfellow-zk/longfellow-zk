import LfzkV2.Native.Prover
import LfzkV2.Native.Events
import LfzkV2.Schedule

/-!
# Native message replay on the shared schedule

`Circuit.shape` retains dimensions and assertion counts so that message roles,
payloads, and hash-prefix geometry can be reused. It is not a translation of
circuit semantics: all evaluations, corrections, and constraints below use the
native circuit. In particular its linear and constant streams are never dropped
from verifier reconstruction.
-/

namespace LfzkV2.Native

open SumcheckV2

variable {F Pad Slot C : Type} [Field F]

def Circuit.shape : {out input : ℕ} → Circuit F out input → LfzkV2.Circuit F out input
  | _, _, .input => .input
  | _, _, .layer a body rest => .layer a
      { ordinary := body.quadratic
        left := fun i => match body.assertions i with
          | .quadratic l _ => l
          | .linear l => l
        right := fun i => match body.assertions i with
          | .quadratic _ r => r
          | .linear l => l }
      rest.shape

omit [Field F] in
theorem Circuit.shape_sharpLayerBudget {out input : ℕ} (circuit : Circuit F out input) :
    circuit.shape.sharpLayerBudget = circuit.sharpLayerBudget := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      simp only [Circuit.shape, LfzkV2.Circuit.sharpLayerBudget, Circuit.sharpLayerBudget, ih]

namespace Replay

abbrev PadPlan {out input : ℕ} (circuit : Circuit F out input) :=
  LfzkV2.Replay.PadPlan (Pad := Pad) (Slot := Slot) circuit.shape
abbrev Payload {out input : ℕ} (circuit : Circuit F out input) :=
  LfzkV2.Replay.Payload circuit.shape

def readFrom (decode : (n : ℕ) → C → Fin n → F) :
    {out input : ℕ} → (circuit : Circuit F out input) →
    PadPlan (Pad := Pad) (Slot := Slot) circuit → Payload circuit → (ℕ → C) → ℕ →
      circuit.Messages Pad Slot
  | _, _, .input, _, _, _, _ => ()
  | _, _, .layer (mid := mid) a _ rest, plan, payload, answers, start =>
      let firstRound := start + LfzkV2.Replay.vectorSlots a
      let messages : LfzkV2.LayerMessages Pad Slot F mid a :=
        { messages := List.ofFn fun i => (payload.1.rounds i, plan.1.round0 i, plan.1.round1 i)
          point i := decode 1 (answers (firstRound + i.val)) 0
          messageA := payload.1.claimA
          messageB := payload.1.claimB
          padA := plan.1.claimA
          padB := plan.1.claimB
          productSlot := plan.1.productSlot
          alpha := decode 1 (answers (firstRound + mid)) 0
          beta := decode a (answers start) }
      (messages, readFrom decode rest plan.2 payload.2 answers (firstRound + mid + 1))

def read (decode : (n : ℕ) → C → Fin n → F) {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) : circuit.Messages Pad Slot :=
  readFrom decode circuit plan payload answers (LfzkV2.Replay.vectorSlots out)

def WellFormed : {out input : ℕ} → (circuit : Circuit F out input) → circuit.Messages Pad Slot → Prop
  | _, _, .input, _ => True
  | _, _, .layer (mid := mid) _ _ rest, messages =>
      messages.1.messages.length = mid ∧ WellFormed rest messages.2

omit [Field F] in
theorem readFrom_wellFormed (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) :
    WellFormed circuit (readFrom decode circuit plan payload answers start) := by
  induction circuit generalizing start with
  | input => trivial
  | layer a body rest ih => exact ⟨List.length_ofFn, ih plan.2 payload.2 _⟩

theorem constraints_total {out input : ℕ} (circuit : Circuit F out input)
    (m : circuit.Messages Pad Slot) (weights : Cube out → F) (hwell : WellFormed circuit m)
    (claim : PadExpression Pad F) :
    ∃ cs, Native.buildFrom claim (circuit.proof m weights) = some cs := by
  induction circuit generalizing claim with
  | input => exact ⟨⟨[], claim⟩, rfl⟩
  | layer a body rest ih =>
      let t := body.transcript weights m.1
      obtain ⟨terminal, hterminal⟩ := LfzkV2.Replay.rounds_total
        (subtractConstant claim t.constant) m.1.messages (List.ofFn m.1.point)
        (hwell.1.trans List.length_ofFn.symm)
      obtain ⟨tail, htail⟩ := ih m.2
        (nextWeights (body.effectiveQuadratic weights m.1.beta)
          (monomialWeights m.1.point) m.1.alpha) hwell.2 t.nextClaim
      dsimp only [t, CircuitLayer.transcript, LfzkV2.LayerMessages.transcript] at hterminal htail
      exact ⟨⟨m.1.transcript.constraint terminal :: tail.layers, tail.inputClaim⟩, by
        simp only [Circuit.proof, Native.buildFrom, CircuitLayer.transcript,
          LfzkV2.LayerMessages.transcript, hterminal, htail]⟩

theorem readFrom_padKeys (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) (weights : Cube out → F) :
    (circuit.proof (readFrom decode circuit plan payload answers start) weights).map
      (fun t => (t.messages.padA, t.messages.padB, t.messages.productSlot)) =
      LfzkV2.Replay.padKeys circuit.shape plan := by
  induction circuit generalizing start with
  | input => rfl
  | layer a body rest ih =>
      change _ :: _ = _ :: _
      congr 1
      exact ih plan.2 payload.2 _ _

theorem read_constraints (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (weights : Cube out → F) :
    ∃ cs, Native.buildConstraints (circuit.proof (read decode circuit plan payload answers) weights) =
        some cs ∧ cs.layers.map (fun c => (c.padA, c.padB, c.productSlot)) =
      LfzkV2.Replay.padKeys circuit.shape plan := by
  obtain ⟨cs, hbuild⟩ := constraints_total circuit _ weights
    (readFrom_wellFormed decode circuit plan payload answers (LfzkV2.Replay.vectorSlots out)) zeroClaim
  exact ⟨cs, hbuild, (Native.buildFrom_products zeroClaim _ cs hbuild).trans
    (readFrom_padKeys decode circuit plan payload answers (LfzkV2.Replay.vectorSlots out) weights)⟩

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

omit [Field F] in
theorem readFrom_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (first second : ℕ → C) (start : ℕ)
    (hanswers : ∀ j, j < start + LfzkV2.Replay.layerSlots circuit.shape → first j = second j) :
    readFrom decode circuit plan payload first start =
      readFrom decode circuit plan payload second start := by
  induction circuit generalizing start with
  | input => rfl
  | @layer out mid input a body rest ih =>
      have hb := decoded_vector_eq decode first second a start
        (start + LfzkV2.Replay.layerSlots (Circuit.layer a body rest).shape)
        (by simp only [Circuit.shape, LfzkV2.Replay.layerSlots]; omega) hanswers
      have hp : (fun i : Fin mid => decode 1 (first (start + LfzkV2.Replay.vectorSlots a + i.val)) 0) =
          (fun i : Fin mid => decode 1 (second (start + LfzkV2.Replay.vectorSlots a + i.val)) 0) := by
        funext i
        rw [hanswers _ (by simp only [Circuit.shape, LfzkV2.Replay.layerSlots]; omega)]
      have ha := hanswers (start + LfzkV2.Replay.vectorSlots a + mid)
        (by simp only [Circuit.shape, LfzkV2.Replay.layerSlots]; omega)
      have hr := ih plan.2 payload.2 (start + LfzkV2.Replay.vectorSlots a + mid + 1) (by
        intro j hj
        apply hanswers j
        simp only [Circuit.shape, LfzkV2.Replay.layerSlots]
        omega)
      dsimp only [readFrom]
      rw [hb, hp, ha, hr]

omit [Field F] in
theorem read_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (first second : ℕ → C)
    (hanswers : ∀ j, j < LfzkV2.Replay.slots circuit.shape → first j = second j) :
    read decode circuit plan payload first = read decode circuit plan payload second :=
  readFrom_eq_of_prefix decode circuit plan payload first second (LfzkV2.Replay.vectorSlots out)
    hanswers

structure Reconstruction {out input : ℕ} (circuit : Circuit F out input) (Pad Slot : Type) where
  messages : circuit.Messages Pad Slot
  point : Fin out → F
  constraints : Constraints Pad Slot F
  built : Native.buildConstraints (circuit.proof messages (monomialWeights point)) = some constraints

noncomputable def reconstructionFromAnswers (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) : Reconstruction circuit Pad Slot where
  messages := read decode circuit plan payload answers
  point := LfzkV2.Replay.outputPoint decode out answers
  constraints := Classical.choose (read_constraints decode circuit plan payload answers
    (monomialWeights (LfzkV2.Replay.outputPoint decode out answers)))
  built := (Classical.choose_spec (read_constraints decode circuit plan payload answers
    (monomialWeights (LfzkV2.Replay.outputPoint decode out answers)))).1

theorem reconstructionFromAnswers_padKeys (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) :
    (reconstructionFromAnswers decode circuit plan payload answers).constraints.layers.map
        (fun c => (c.padA, c.padB, c.productSlot)) = LfzkV2.Replay.padKeys circuit.shape plan :=
  (Classical.choose_spec (read_constraints decode circuit plan payload answers
    (monomialWeights (LfzkV2.Replay.outputPoint decode out answers)))).2

@[ext] theorem Reconstruction.ext {out input : ℕ} {circuit : Circuit F out input}
    {first second : Reconstruction circuit Pad Slot}
    (hmessages : first.messages = second.messages) (hpoint : first.point = second.point)
    (hconstraints : first.constraints = second.constraints) : first = second := by
  cases first
  cases second
  cases hmessages
  cases hpoint
  cases hconstraints
  rfl

theorem reconstructionFromAnswers_eq_of_prefix (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (first second : ℕ → C)
    (hanswers : ∀ j, j < LfzkV2.Replay.slots circuit.shape → first j = second j) :
    reconstructionFromAnswers decode circuit plan payload first =
      reconstructionFromAnswers decode circuit plan payload second := by
  have hm : read decode circuit plan payload first = read decode circuit plan payload second :=
    readFrom_eq_of_prefix decode circuit plan payload first second (LfzkV2.Replay.vectorSlots out)
      hanswers
  have hp : LfzkV2.Replay.outputPoint decode out first =
      LfzkV2.Replay.outputPoint decode out second :=
    decoded_vector_eq decode first second out 0 (LfzkV2.Replay.slots circuit.shape)
      (by simp only [LfzkV2.Replay.slots]; omega) hanswers
  apply Reconstruction.ext hm hp
  apply Option.some.inj
  rw [← (reconstructionFromAnswers decode circuit plan payload first).built,
    ← (reconstructionFromAnswers decode circuit plan payload second).built]
  exact congrArg Native.buildConstraints (by
    dsimp only [reconstructionFromAnswers]
    rw [hm, hp])

end Replay

end LfzkV2.Native
