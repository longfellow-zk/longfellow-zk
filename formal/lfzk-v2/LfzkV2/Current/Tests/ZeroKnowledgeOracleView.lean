import LfzkV2.Current.ZeroKnowledge.OracleView
import LfzkV2.Current.ZeroKnowledge.MerkleRuntime

namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleView
open Merkle.RandomOracle ZeroKnowledge

/-- The same two queries can be recorded in the proof view without making
a third oracle query, including when both queries name the same input. -/
example {Query Answer : Type} (query : Query) (H : Query → Answer) :
    ((OracleView.record (Tree.query query fun _ => Tree.query query fun answer =>
      Tree.done (fuel := 0) answer)).run H).1 =
        (H query,[(query,H query),(query,H query)]) := by
  rw [OracleView.record_output]
  rfl

#print axioms OracleView.record_run
#print axioms MerkleRuntime.codec_inj
#print axioms MerkleRuntime.physicalLeaf

end LfzkV2.Current.Tests.ZeroKnowledgeOracleView
