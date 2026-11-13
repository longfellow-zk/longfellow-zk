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

end LfzkV2.Current.ZeroKnowledge.Frontend.PayloadTransport
