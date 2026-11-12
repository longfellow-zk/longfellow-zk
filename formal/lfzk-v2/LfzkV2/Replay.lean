import LfzkV2.ReplayPrimitives
import LfzkV2.Prover
import LfzkV2.ChallengeBlocks

/-!
# V2 verification from proof payloads and whole challenge answers

The trusted pad plan is fixed before commitment. The proof supplies exactly
two coefficients per round and two final claims per layer. Output and
assertion vectors consume one answer each when nonempty; every sumcheck
round and every final-claim combination consumes one answer.
-/

namespace LfzkV2.Replay

open SumcheckV2

variable {F Pad Slot C : Type} [Field F]

structure LayerPayload (F : Type) (rounds : ℕ) where
  rounds : Fin rounds → RoundPoly F
  claimA : F
  claimB : F

abbrev PadPlan : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) _ _ rest => LayerPads Pad Slot mid × PadPlan rest

abbrev Payload : {out input : ℕ} → Circuit F out input → Type
  | _, _, .input => Unit
  | _, _, .layer (mid := mid) _ _ rest => LayerPayload F mid × Payload rest

def layerSlots : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) assertions _ rest => vectorSlots assertions + mid + 1 + layerSlots rest

def slots {out input : ℕ} (circuit : Circuit F out input) : ℕ := vectorSlots out + layerSlots circuit

def readFrom (decode : (n : ℕ) → C → Fin n → F) :
    {out input : ℕ} → (circuit : Circuit F out input) →
    PadPlan (Pad := Pad) (Slot := Slot) circuit → Payload circuit → (ℕ → C) → ℕ →
      circuit.Messages Pad Slot
  | _, _, .input, _, _, _, _ => ()
  | _, _, .layer (mid := mid) assertions _ rest, plan, payload, answers, start =>
      let firstRound := start + vectorSlots assertions
      let messages : LayerMessages Pad Slot F mid assertions :=
        { messages := List.ofFn fun i => (payload.1.rounds i, plan.1.round0 i, plan.1.round1 i)
          point i := decode 1 (answers (firstRound + i.val)) 0
          messageA := payload.1.claimA
          messageB := payload.1.claimB
          padA := plan.1.claimA
          padB := plan.1.claimB
          productSlot := plan.1.productSlot
          alpha := decode 1 (answers (firstRound + mid)) 0
          beta := decode assertions (answers start) }
      (messages, readFrom decode rest plan.2 payload.2 answers (firstRound + mid + 1))

def read (decode : (n : ℕ) → C → Fin n → F) {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) : circuit.Messages Pad Slot :=
  readFrom decode circuit plan payload answers (vectorSlots out)

def WellFormed : {out input : ℕ} → (circuit : Circuit F out input) → circuit.Messages Pad Slot → Prop
  | _, _, .input, _ => True
  | _, _, .layer (mid := mid) _ _ rest, messages =>
      messages.1.messages.length = mid ∧ WellFormed rest messages.2

omit [Field F] in
theorem readFrom_wellFormed (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) : WellFormed circuit (readFrom decode circuit plan payload answers start) := by
  induction circuit generalizing start with
  | input => trivial
  | layer a body rest ih =>
      exact ⟨List.length_ofFn, ih plan.2 payload.2 _⟩

theorem constraints_total {out input : ℕ} (circuit : Circuit F out input)
    (messages : circuit.Messages Pad Slot) (hwell : WellFormed circuit messages)
    (claim : PadExpression Pad F) : ∃ cs, buildFrom claim (circuit.proof messages) = some cs := by
  induction circuit generalizing claim with
  | input => exact ⟨⟨[],claim⟩,rfl⟩
  | layer a body rest ih =>
      obtain ⟨terminal,hterminal⟩ := rounds_total claim messages.1.messages
        (List.ofFn messages.1.point) (hwell.1.trans List.length_ofFn.symm)
      obtain ⟨tail,htail⟩ := ih messages.2 hwell.2 messages.1.transcript.nextClaim
      dsimp only [LayerMessages.transcript] at htail
      exact ⟨⟨messages.1.transcript.constraint terminal :: tail.layers,tail.inputClaim⟩, by
        simp only [Circuit.proof, buildFrom, LayerMessages.transcript, hterminal, htail]⟩

def padKeys : {out input : ℕ} → (circuit : Circuit F out input) →
    PadPlan (Pad := Pad) (Slot := Slot) circuit → List (Pad × Pad × Slot)
  | _, _, .input, _ => []
  | _, _, .layer _ _ rest, plan =>
      (plan.1.claimA,plan.1.claimB,plan.1.productSlot) :: padKeys rest plan.2

omit [Field F] in
theorem readFrom_padKeys (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) (start : ℕ) :
    (circuit.proof (readFrom decode circuit plan payload answers start)).map
      (fun t => (t.padA,t.padB,t.productSlot)) = padKeys circuit plan := by
  induction circuit generalizing start with
  | input => rfl
  | layer a body rest ih =>
      change _ :: _ = _ :: _
      congr 1
      exact ih plan.2 payload.2 _

/-- Every correctly shaped proof reconstructs constraints, and their product
keys depend only on the public plan, not on messages or oracle answers. -/
theorem read_constraints (decode : (n : ℕ) → C → Fin n → F)
    {out input : ℕ} (circuit : Circuit F out input)
    (plan : PadPlan (Pad := Pad) (Slot := Slot) circuit) (payload : Payload circuit)
    (answers : ℕ → C) :
    ∃ cs, buildConstraints (circuit.proof (read decode circuit plan payload answers)) = some cs ∧
      cs.layers.map (fun c => (c.padA,c.padB,c.productSlot)) = padKeys circuit plan := by
  obtain ⟨cs,hbuild⟩ := constraints_total circuit _
    (readFrom_wellFormed decode circuit plan payload answers (vectorSlots out)) zeroClaim
  exact ⟨cs,hbuild,(buildFrom_products zeroClaim _ cs hbuild).trans
    (readFrom_padKeys decode circuit plan payload answers (vectorSlots out))⟩

end LfzkV2.Replay
