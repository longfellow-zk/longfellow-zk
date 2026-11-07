import LfzkV2.Current.ZeroKnowledge.HonestTranscriptProgress
import LfzkV2.Current.ZeroKnowledge.OracleRefreshHybrid

/-! The honest sumcheck is a causal bounded tree, including its complete
payload/replay state. An input-only continuation extends the existing answer
and introduces no additional query. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeHonestTranscript
open Merkle.RandomOracle SumcheckV2 ZeroKnowledge

example {F State Query Answer : Type} [Field F] (queries : HonestTranscript.Queries F State Query Answer)
    (w weights : Cube 0 → F) (state : State) (H : Query → Answer) :
    ((HonestTranscript.circuit queries (FrontendSchedule.Plan.input : FrontendSchedule.Plan F (.input (n := 0)))
      (Pad := Empty) () w weights state () true).run H).2 = [] := rfl

#print axioms HonestTranscript.complete_reader
#print axioms HonestTranscript.rounds_output
#print axioms HonestTranscript.layer_output
#print axioms HonestTranscript.circuit_output
#print axioms HonestTranscript.complete_progress
#print axioms HonestTranscript.circuit_progress
#print axioms OracleRefresh.programmed_eq_guarded
#print axioms OracleRefresh.guarded_sameDistribution

end LfzkV2.Current.Tests.ZeroKnowledgeHonestTranscript
