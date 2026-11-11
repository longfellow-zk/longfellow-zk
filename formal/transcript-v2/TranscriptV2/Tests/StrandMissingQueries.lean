import TranscriptV2.StrandMissingQueries

/-! Axiom audits and regressions for position-based charging. In particular,
input independence must survive a completely colliding hash oracle. -/
namespace TranscriptV2.Tests.StrandMissingQueries
open Strand Framing StrandLinear

example (messages : ℕ → Bytes) (digest : Digest) :
    (replay messages (fun _ => digest) 0).input.encode ≠
      (replay messages (fun _ => digest) 1).input.encode :=
  replay_inputs_ne messages _ 0 1 (by decide) (by decide) (by decide)

example (messages : ℕ → Bytes) (H : Oracle) (replacement : Digest) :
    replay messages H 3 =
      replay messages (Function.update H (replay messages H 3).input.encode replacement) 3 := by
  apply replay_off messages H _ 3 (by decide)
  intro input different
  rw [Function.update_of_ne different]

example (trace : StrandRecovery.Trace) (digest : Digest) :
    StrandRecovery.target trace 7 digest 7 = some digest :=
  StrandRecovery.target_self trace 7 digest

#print axioms StrandLinear.replay_off
#print axioms StrandLinear.replay_restrict_off
#print axioms StrandRecovery.missing_node
#print axioms StrandRecovery.sealTarget_of_mem
#print axioms TranscriptV2.StrandMissingQueries.missing_covered
#print axioms TranscriptV2.StrandMissingQueries.hit_density_le
#print axioms TranscriptV2.StrandMissingQueries.missing_density_le

end TranscriptV2.Tests.StrandMissingQueries
