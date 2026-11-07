import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalPrefix

/-! The generated state retains exactly the writes, links and answers that
created its history. This invariant is independent of the eventual proof
body. Consequently the encoder comparison can be made after all frontend
messages have been generated, without giving earlier rounds future data. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.History

open SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)

def Valid (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
    (Fin i.val → C) → Base)
    (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
    (context : Key) : (n : ℕ) → n ≤ g.roles.length →
    Current.History Key (Base × ProtocolWrites.Fresh g fields Advice) Digest n →
    (Fin n → C) → (Fin n → ProtocolWrites.Fresh g fields Advice) → Prop
  | 0,_,history,_,_ => history = context
  | n+1,bound,history,past,writes =>
      Valid base H context n (by omega) history.1 (fun i => past i.castSucc) (fun i => writes i.castSucc) ∧
        history.2.1 = (base ⟨n,by omega⟩ writes (fun i => past i.castSucc),writes (Fin.last n)) ∧
        H (.round ⟨n,by omega⟩ history.1 history.2.1) = (history.2.2,past (Fin.last n))

def Good (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C) : Prop :=
  Valid base H context state.rank.val (by have := state.rank.isLt; omega)
    state.history state.past state.writes

theorem initial_good (context : Key) (fallback : C) :
    Good base H context (CompleteTranscript.initial context fallback) := rfl

theorem bind_good (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (write : ProtocolWrites.Fresh g fields Advice → ProtocolWrites.Fresh g fields Advice)
    (good : Good base H context state) :
    Good base H context (CompleteTranscript.bind state write) := good

theorem advance_good (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (good : Good base H context state) :
    Good base H context (CompleteTranscript.advance base state inside
      (H (CompleteTranscript.query base state inside))) := by
  simpa only [Good,CompleteTranscript.advance,Valid,Fin.snoc_castSucc,Fin.snoc_last,
    CompleteTranscript.currentBlock,CompleteTranscript.query] using
    (show Good base H context state ∧
      CompleteTranscript.currentBlock base state inside =
        (base ⟨state.rank.val,inside⟩ (Fin.snoc state.writes state.pending) state.past,state.pending) ∧
      H (CompleteTranscript.query base state inside) = H (CompleteTranscript.query base state inside)
      from ⟨good,rfl,rfl⟩)

theorem step_good (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (good : Good base H context state) : Good base H context (CompleteTranscript.step base H state).2 := by
  by_cases inside : state.rank.val < g.roles.length
  · rw [CompleteTranscript.step_query base H state inside]
    exact advance_good base H context state inside good
  · simpa only [CompleteTranscript.step,dif_neg inside] using good

theorem execute_good {F : Type} (side : Side) (field : fields side ≃ F)
    (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (messages : List (Option (Layered.Replay.Message F)))
    (good : Good base H context state) :
    Good base H context (Prefix.execute side field base H state messages) := by
  induction messages generalizing state with
  | nil => exact good
  | cons message tail ih =>
      apply ih
      apply step_good
      cases message with
      | none => exact good
      | some message => exact bind_good base H context state _ good

theorem circuit_good {F Pad : Type} [Field F] (side : Side) (field : fields side ≃ F)
    (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0})
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit) (continuing : Bool)
    (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (good : Good base H context state) :
    Good base H context (readSetup (CompleteTranscript.reader side field decode nonzero base H)
      plan ids payload state continuing).2 := by
  rw [Prefix.circuit_state]
  exact execute_good base H side field context state _ good

theorem valid_past (context : Key) (n : ℕ) (bound : n ≤ g.roles.length)
    (history : Current.History Key (Base × ProtocolWrites.Fresh g fields Advice) Digest n)
    (past : Fin n → C) (writes : Fin n → ProtocolWrites.Fresh g fields Advice)
    (valid : Valid base H context n bound history past writes) (i : Fin n) :
    past i = (H (Input.historyPoints n bound history i)).2 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Input.historyPoints,Fin.snoc_last]
        exact (congrArg Prod.snd valid.2.2).symm
      · simp only [Input.historyPoints,Fin.snoc_castSucc]
        exact ih (by omega) history.1 (fun k => past k.castSucc) (fun k => writes k.castSucc) valid.1 j

theorem query_past (context : Key) (state : CompleteTranscript.State g fields Advice Key Base C)
    (inside : state.rank.val < g.roles.length) (good : Good base H context state) :
    state.past = (CompleteTranscript.query (Authentication := Authentication) base state inside).priorAnswers H := by
  funext i
  exact valid_past base H context state.rank.val (by have := state.rank.isLt; omega)
    state.history state.past state.writes good i

set_option backward.isDefEq.respectTransparency false in
/-- Once the stored write prefix is identified, the entire generated
history is the verifier's canonical replay. No earlier call receives the
future write vector; it is used only to establish this final identity. -/
theorem valid_replay
    (e : Replay.Encoding g fields Advice Authentication Key
      (Base × ProtocolWrites.Fresh g fields Advice) C)
    (proof : Replay.Output g fields Advice Authentication) (initialLink : Digest)
    (allWrites : Fin g.roles.length → ProtocolWrites.Fresh g fields Advice)
    (blocks : ∀ (i : Fin g.roles.length) (past : Fin i.val → C),
      e.block proof i past =
        (base i (fun j => allWrites ⟨j.val,by have := j.isLt; have := i.isLt; omega⟩) past,allWrites i))
    (n : ℕ) (bound : n ≤ g.roles.length)
    (history : Current.History Key (Base × ProtocolWrites.Fresh g fields Advice) Digest n)
    (past : Fin n → C) (writes : Fin n → ProtocolWrites.Fresh g fields Advice)
    (valid : Valid base H (e.context proof) n bound history past writes)
    (written : ∀ i, writes i = allWrites ⟨i.val,i.isLt.trans_le bound⟩) :
    e.stateAt proof n bound history past = (e.chain initialLink).replay proof H n := by
  induction n with
  | zero =>
      change history = e.context proof at valid
      subst history
      have empty : past = Fin.elim0 := Subsingleton.elim _ _
      subst past
      rfl
  | succ n ih =>
      have inside : n < g.roles.length := by omega
      have prior := ih (by omega) history.1 (fun i => past i.castSucc)
        (fun i => writes i.castSucc) valid.1 (fun i => written i.castSucc)
      have hw : writes = fun j => allWrites ⟨j.val,j.isLt.trans_le bound⟩ := funext written
      have block : e.block proof ⟨n,inside⟩ (fun i => past i.castSucc) = history.2.1 := by
        rw [blocks,valid.2.1,hw]
        rfl
      have current : e.stateAt proof n (by omega) history.1 (fun i => past i.castSucc) =
          ⟨.round ⟨n,inside⟩ history.1 history.2.1,fun i => past i.castSucc⟩ := by
        have atState : e.stateAt proof n (by omega) history.1 (fun i => past i.castSucc) =
            ⟨.round ⟨n,inside⟩ history.1 (e.block proof ⟨n,inside⟩ (fun i => past i.castSucc)),
              fun i => past i.castSucc⟩ := dif_pos inside
        rw [atState,block]
      rw [TranscriptV2.Chain.replay,dif_pos inside]
      change _ = e.advance proof ((e.chain initialLink).replay proof H n)
        (H (((e.chain initialLink).replay proof H n).point))
      rw [← prior,current]
      change e.stateAt proof (n+1) bound history past =
        e.stateAt proof (n+1) _
          (history.1,history.2.1,(H (.round ⟨n,inside⟩ history.1 history.2.1)).1)
          (Fin.snoc (fun i => past i.castSucc) (H (.round ⟨n,inside⟩ history.1 history.2.1)).2)
      rw [valid.2.2]
      congr 1
      exact (Fin.snoc_init_self past).symm

end LfzkV2.Current.ZeroKnowledge.Frontend.History
