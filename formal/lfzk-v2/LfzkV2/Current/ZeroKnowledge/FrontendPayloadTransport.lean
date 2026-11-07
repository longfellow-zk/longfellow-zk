import LfzkV2.Current.ZeroKnowledge.FrontendParser

/-! Generated adapter coefficients preserve the public payload encoding.
The proof goes through the actual optional-write stream, so entry-only and
shared terminal boundaries receive no artificial message or query. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.PayloadTransport
open SumcheckV2
open scoped Classical
variable {F : Type} [Field F]

omit [Field F] in
theorem circuit_injective {out input : ℕ} {circuit : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F circuit) :
    Function.Injective (fun payload : Layered.Replay.Payload circuit => Prefix.circuit plan payload false) := by
  intro first second same
  change Prefix.circuit plan first false = Prefix.circuit plan second false at same
  have parsed : ApplicationPrefix.Messages.read circuit (fun q => some (FrontendTranscript.write circuit first q)) =
      ApplicationPrefix.Messages.read circuit (fun q => some (FrontendTranscript.write circuit second q)) := by
    apply ApplicationPrefix.Messages.readFrom_congr
    intro q _ bound
    have a := Prefix.circuit_wire plan first q (by omega)
    have b := Prefix.circuit_wire plan second q (by omega)
    rw [same] at a
    exact a.symm.trans b
  rw [ApplicationPrefix.Messages.read_write,ApplicationPrefix.Messages.read_write] at parsed
  exact Option.some.inj parsed

omit [Field F] in
theorem same_body {out input : ℕ} {first second : Layered.Circuit F out input}
    (plan : FrontendSchedule.Plan F first) (same : FrontendTopology.Same first second)
    (payload : Layered.Replay.Payload first) :
    (CompleteShape.bodyEquiv (same.plan plan)).symm
      (Eq.mp (congrArg (FrontendPayload F) (same.frontend plan).symm) (CompleteShape.bodyEquiv plan payload)) =
      CompleteShape.payloadEquiv same payload := by
  let decoded := (CompleteShape.bodyEquiv (same.plan plan)).symm
    (Eq.mp (congrArg (FrontendPayload F) (same.frontend plan).symm) (CompleteShape.bodyEquiv plan payload))
  have encoded : Eq.mp (congrArg (FrontendPayload F) (same.frontend plan).symm) (CompleteShape.bodyEquiv plan payload) =
      CompleteShape.bodyEquiv (same.plan plan) decoded :=
    (CompleteShape.bodyEquiv (same.plan plan)).apply_symm_apply _ |>.symm
  have stream := Parser.role_stream_cast plan.frontend (same.plan plan).frontend (same.frontend plan).symm
    .binary (CompleteShape.bodyEquiv plan payload)
  rw [encoded,← Prefix.circuit_roles,← Prefix.circuit_roles] at stream
  apply circuit_injective (same.plan plan)
  exact stream.symm.trans (Prefix.circuit_same plan same payload false).symm

end LfzkV2.Current.ZeroKnowledge.Frontend.PayloadTransport
