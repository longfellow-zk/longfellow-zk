import LfzkV2.Current.ZeroKnowledge.OracleRequestedRawNormalization

/-! The semantic oracle-result boundary preserves aborts, complete public
outputs and every observable transcript coordinate. Actual requested
callbacks and their raw observer transports are included in this audit. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleNormalization
open ZeroKnowledge OracleResults

example {Point Answer Public : Type} (valid : Set Point)
    (output : Public × (Point → Answer))
    (same : SameCompletion valid none (some output)) : False := by
  cases same.relation

example {Point Answer Public MerkleQuery MerkleAnswer : Type}
    (HM : MerkleQuery → MerkleAnswer) (H : Point → Answer) :
    totalize (Public := Public) HM H none = (none,(HM,H)) := rfl

#print axioms OracleResults.Same.trans
#print axioms OracleResults.Same.visible_eq
#print axioms OracleResults.SameCompletion.mono
#print axioms OracleResults.SameCompletion.public_eq
#print axioms OracleResults.SameCompletion.abort_eq
#print axioms OracleResults.SameCompletion.totalize
#print axioms OracleNormalization.replay_eq
#print axioms OracleNormalization.program_eq
#print axioms OracleCompleteNormalization.complete_eq
#print axioms OracleSimulatorNormalization.simulate_eq
#print axioms OracleHonestRuntimeNormalization.prove_original_eq
#print axioms OracleRequestedNormalization.simulated_eq
#print axioms OracleRequestedNormalization.honest_eq
#print axioms OracleRawNormalization.experiment_eq_of_results
#print axioms OracleRawNormalization.experiment_eq_at_result
#print axioms OracleRequestedRawNormalization.simulated_raw_eq
#print axioms OracleRequestedRawNormalization.honest_raw_eq
#print axioms OracleRequestedRawNormalization.honest_raw_eq_at

end LfzkV2.Current.Tests.ZeroKnowledgeOracleNormalization
