import LfzkV2.Current.ZeroKnowledge.FrontendCompleteWire

/-! Flatten the frontend reader into its actual boundary writes. A missing
message denotes the shared assertion boundary, which may already carry the
fingerprint responses or adapter advice. Input assertions after the final
combine only extend that answer and therefore add no list entry.

These are identities for the existing stateful reader, independent of any
honest-witness or privacy premise. They allow its generated prefix to be
compared with the complete proof encoder one boundary at a time. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.Prefix

open SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable {F Pad : Type} [Field F]
local notation "State" => CompleteTranscript.State g fields Advice Key Base C
local notation "Point" => CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

def prepare (state : State) : Option (Layered.Replay.Message F) → State
  | none => state
  | some message => CompleteTranscript.frontend side state
      (CompleteTranscript.mapMessage field.symm message)

def execute (side : Side) (field : fields side ≃ F)
    (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
      (Fin i.val → C) → Base) (H : Point → Digest × C) :
    State → List (Option (Layered.Replay.Message F)) → State
  | state, [] => state
  | state, message :: tail =>
      execute side field base H (CompleteTranscript.step base H (prepare side field state message)).2 tail


omit [Field F] in
theorem execute_append (state : State) (first second : List (Option (Layered.Replay.Message F))) :
    execute side field base H state (first++second) =
      execute side field base H (execute side field base H state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons head tail ih => exact ih _

def rounds {n : ℕ} (messages : Fin n → RoundPoly F) : List (Option (Layered.Replay.Message F)) :=
  List.ofFn fun i => some (.round (messages i))

def layer {n : ℕ} (payload : LayerPayload F n) : List (Option (Layered.Replay.Message F)) :=
  rounds payload.rounds ++ [some (.cross payload.cross),some (.claims payload.claimA payload.claimB)]

def circuit : {out input : ℕ} → {body : Layered.Circuit F out input} →
    FrontendSchedule.Plan F body → Layered.Replay.Payload body → Bool →
      List (Option (Layered.Replay.Message F))
  | _,_,_,.input,_,continuing => if continuing then [] else [none]
  | _,_,_,.inputEntry ..,_,continuing => if continuing then [] else [none]
  | _,_,_,.layer _ tail,payload,_ => none :: layer payload.1 ++ circuit tail payload.2 true
  | _,_,_,.entryLayer _ _ _ tail,payload,_ => none :: layer payload.1 ++ circuit tail payload.2 true

omit [Field F] in
theorem circuit_same {out input : ℕ} {first second : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F first) (same : FrontendTopology.Same first second)
    (payload : Layered.Replay.Payload first) (continuing : Bool) :
    circuit (same.plan plan) (CompleteShape.payloadEquiv same payload) continuing =
      circuit plan payload continuing := by
  induction plan generalizing continuing with
  | input => cases same; rfl
  | inputEntry =>
      cases same with
      | entry tail => cases tail; rfl
  | layer _ _ ih =>
      cases same with
      | layer _ next =>
          simp only [FrontendTopology.Same.plan,CompleteShape.payloadEquiv,circuit,
            Equiv.prodCongr_apply]
          change none :: layer payload.1 ++
            circuit (next.plan _) (CompleteShape.payloadEquiv next payload.2) true = _
          rw [ih next]
  | entryLayer _ _ _ _ ih =>
      cases same with
      | entry next =>
          cases next with
          | layer _ rest =>
              simp only [FrontendTopology.Same.plan,CompleteShape.payloadEquiv,circuit,
                Equiv.prodCongr_apply]
              change none :: layer payload.1 ++
                circuit (rest.plan _) (CompleteShape.payloadEquiv rest payload.2) true = _
              rw [ih rest]

variable (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})

theorem rounds_state {n : ℕ} (state : State) (messages : Fin n → RoundPoly F) :
    (readRounds (CompleteTranscript.reader side field decode nonzero base H).toReader state messages).2 =
      execute side field base H state (rounds messages) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [readRounds,rounds,List.ofFn_succ,execute]
      exact ih _ _

theorem layer_state {n : ℕ} (state : State) (payload : LayerPayload F n) :
    (readLayer (CompleteTranscript.reader side field decode nonzero base H).toReader state payload).state =
      execute side field base H state (layer payload) := by
  simp only [readLayer,rounds_state,layer,execute_append,execute,prepare]
  rfl

theorem circuit_state {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (payload : Layered.Replay.Payload body) (state : State) (continuing : Bool) :
    (readSetup (CompleteTranscript.reader side field decode nonzero base H)
      plan ids payload state continuing).2 =
        execute side field base H state (circuit plan payload continuing) := by
  induction plan generalizing state continuing with
  | input => cases continuing <;> rfl
  | inputEntry => cases continuing <;> rfl
  | layer _ tail ih =>
      dsimp only [readSetup,circuit]
      rw [ih,layer_state,execute_append]
      rfl
  | entryLayer _ _ _ tail ih =>
      dsimp only [readSetup,circuit]
      rw [ih,layer_state,execute_append]
      rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.Prefix
