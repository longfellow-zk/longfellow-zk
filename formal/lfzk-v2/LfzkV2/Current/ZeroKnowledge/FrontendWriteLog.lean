import LfzkV2.Current.ZeroKnowledge.FrontendPrefix

/-! The finite log of fresh writes in a generated transcript. Recording a
boundary appends precisely its pending write; all later boundaries begin
with an empty pending write. This isolates message bookkeeping from oracle
answers and from the canonical byte encoder. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.WriteLog

open SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F : Type}
variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

def empty : ProtocolWrites.Fresh g fields Advice := {}

def log (state : CompleteTranscript.State g fields Advice Key Base C) :
    List (ProtocolWrites.Fresh g fields Advice) := List.ofFn state.writes

theorem bind_log (state : CompleteTranscript.State g fields Advice Key Base C)
    (write : ProtocolWrites.Fresh g fields Advice → ProtocolWrites.Fresh g fields Advice) :
    log (CompleteTranscript.bind state write) = log state := rfl

def withMessage (pending : ProtocolWrites.Fresh g fields Advice) :
    Option (Layered.Replay.Message F) → ProtocolWrites.Fresh g fields Advice
  | none => pending
  | some message =>
      { pending with frontend := Function.update pending.frontend side (CompleteTranscript.mapMessage field.symm message) }

def snapshots (side : Side) (field : fields side ≃ F) :
    ProtocolWrites.Fresh g fields Advice → List (Option (Layered.Replay.Message F)) →
      List (ProtocolWrites.Fresh g fields Advice)
  | _, [] => []
  | pending,head::tail => withMessage side field pending head :: snapshots side field {} tail

theorem prepare_log (state : CompleteTranscript.State g fields Advice Key Base C)
    (message : Option (Layered.Replay.Message F)) :
    log (Prefix.prepare side field state message) = log state := by
  cases message <;> rfl

theorem prepare_pending (state : CompleteTranscript.State g fields Advice Key Base C)
    (message : Option (Layered.Replay.Message F)) :
    (Prefix.prepare side field state message).pending = withMessage side field state.pending message := by
  cases message <;> rfl

theorem prepare_rank (state : CompleteTranscript.State g fields Advice Key Base C)
    (message : Option (Layered.Replay.Message F)) :
    (Prefix.prepare side field state message).rank = state.rank := by
  cases message <;> rfl

theorem advance_log (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (answer : Digest × C) :
    log (CompleteTranscript.advance base state inside answer) = log state ++ [state.pending] := by
  simp only [log,CompleteTranscript.advance,List.ofFn_succ',Fin.snoc_castSucc,Fin.snoc_last,
    List.concat_eq_append]

theorem step_log (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) :
    log (CompleteTranscript.step base H state).2 = log state ++ [state.pending] := by
  rw [CompleteTranscript.step_query base H state inside]
  exact advance_log base state inside _

theorem step_pending (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) :
    (CompleteTranscript.step base H state).2.pending = {} := by
  rw [CompleteTranscript.step_query base H state inside]
  rfl

theorem execute_log (state : CompleteTranscript.State g fields Advice Key Base C)
    (messages : List (Option (Layered.Replay.Message F)))
    (fits : state.rank.val+messages.length ≤ g.roles.length) :
    log (Prefix.execute side field base H state messages) =
      log state ++ snapshots side field state.pending messages := by
  induction messages generalizing state with
  | nil => simp only [Prefix.execute,snapshots,List.append_nil]
  | cons head tail ih =>
      have inside : (Prefix.prepare side field state head).rank.val < g.roles.length := by
        rw [prepare_rank]
        simp only [List.length_cons] at fits
        omega
      rw [Prefix.execute,CompleteTranscript.step_query base H _ inside]
      rw [ih _ (by
        change (Prefix.prepare side field state head).rank.val+1+tail.length ≤ g.roles.length
        rw [prepare_rank]
        simp only [List.length_cons] at fits
        omega)]
      change log (CompleteTranscript.advance base (Prefix.prepare side field state head) inside _)
          ++ snapshots side field {} tail = _
      rw [advance_log,prepare_log,prepare_pending]
      simp only [snapshots,List.append_assoc,List.singleton_append]

theorem execute_pending (state : CompleteTranscript.State g fields Advice Key Base C)
    (messages : List (Option (Layered.Replay.Message F))) (nonempty : messages ≠ [])
    (fits : state.rank.val+messages.length ≤ g.roles.length) :
    (Prefix.execute side field base H state messages).pending = {} := by
  induction messages generalizing state with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      have inside : (Prefix.prepare side field state head).rank.val < g.roles.length := by
        rw [prepare_rank]
        simp only [List.length_cons] at fits
        omega
      rw [Prefix.execute,CompleteTranscript.step_query base H _ inside]
      cases tail with
      | nil => rfl
      | cons next rest =>
          exact ih _ (by simp) (by
            change (Prefix.prepare side field state head).rank.val+1+(next::rest).length ≤ g.roles.length
            rw [prepare_rank]
            simp only [List.length_cons] at fits ⊢
            omega)

theorem circuit_nonempty {F : Type} [Field F] {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (payload : Layered.Replay.Payload body) :
    Prefix.circuit plan payload false ≠ [] := by
  cases plan <;> simp [Prefix.circuit]

theorem circuit_log [Field F] {Pad : Type} (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (payload : Layered.Replay.Payload body) (continuing : Bool)
    (state : CompleteTranscript.State g fields Advice Key Base C)
    (fits : state.rank.val+(Prefix.circuit plan payload continuing).length ≤ g.roles.length) :
    log (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state continuing).2 =
      log state ++ snapshots side field state.pending (Prefix.circuit plan payload continuing) := by
  rw [Prefix.circuit_state]
  exact execute_log side field base H state _ fits

theorem circuit_pending [Field F] {Pad : Type} (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    {out input : ℕ} {body : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F body) (ids : Layered.Replay.PadPlan (Pad := Pad) body)
    (payload : Layered.Replay.Payload body)
    (state : CompleteTranscript.State g fields Advice Key Base C)
    (fits : state.rank.val+(Prefix.circuit plan payload false).length ≤ g.roles.length) :
    (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).2.pending = {} := by
  rw [Prefix.circuit_state]
  exact execute_pending side field base H state _ (circuit_nonempty plan payload) fits

end LfzkV2.Current.ZeroKnowledge.Frontend.WriteLog
