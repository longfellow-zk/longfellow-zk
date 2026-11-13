import LfzkV2.Current.ZeroKnowledge.FrontendSetupAnswerTape

/-! Stateful frontend reconstruction and the runtime verifier feed the same
messages to the affine compiler. The answer window below is read from the
actual future transcript state; extending that state does not resample any
challenge. Shared assertion boundaries retain their coordinate offsets. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CompilerTransport
open SumcheckV2
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C F Pad : Type} [Field F]
variable (side : Side) (field : fields side ≃ F)
variable (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)
variable (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
variable (decode : C → ℕ → F) (nonzero : C → {r : F // r ≠ 0}) (fallback : C)

theorem messages {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) (ids : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Layered.Replay.Payload circuit)
    (state future : CompleteTranscript.State g fields Advice Key Base C)
    (fits : state.rank.val+Frontend.ScheduleLength.circuitFuel plan false ≤ g.roles.length)
    (extended : AnswerTape.Extends fallback
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).2 future) :
    messagesFromSetup circuit
      (readSetup (CompleteTranscript.reader side field decode nonzero base H) plan ids payload state false).1 payload =
      FrontendReplay.read decode nonzero circuit ids payload
        (fun q => AnswerTape.lookup fallback future (state.rank.val+q)) := by
  rw [AnswerTape.readSetup_initial_into side field base H decode nonzero fallback plan ids payload state future fits extended]
  simpa only [Nat.add_zero,FrontendReplay.read] using
    AnswerTape.replay_shift decode nonzero circuit ids payload (AnswerTape.lookup fallback future) state.rank.val 0 0

end LfzkV2.Current.ZeroKnowledge.Frontend.CompilerTransport
