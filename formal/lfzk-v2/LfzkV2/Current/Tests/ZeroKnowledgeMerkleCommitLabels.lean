import LfzkV2.Current.ZeroKnowledge.MerkleCommitLabels

/-! Heap slots are sampled in actual commitment order, while parents read
only the child slots already processed by that traversal. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitLabels

open ZeroKnowledge.MerkleCommitRefresh

example (request : Bool) (tape : Fin 3 → Bool) :
    (sampledState 2 request tape 1 (by decide)).2 3 = tape 0 := by
  exact sampled_processed 2 request tape 1 (by decide) 3 (by decide) (by decide)

example (request : Bool) (tape : Fin 3 → Bool) :
    (sampledState 2 request tape 3 (by decide)).2 1 = tape 2 := by
  exact sampled_processed 2 request tape 3 (by decide) 1 (by decide) (by decide)

example (request : Bool) (tape : Fin 3 → Bool) :
    (sampledState 2 request tape 1 (by decide)).2 1 = false := by
  exact sampled_unprocessed 2 request tape 1 (by decide) 1 (Or.inl (by decide))

#print axioms sampled_request
#print axioms sampled_processed
#print axioms sampled_unprocessed
#print axioms sampledInput_leaf
#print axioms sampledInput_node
#print axioms sampledInput_commitInput
#print axioms sampledInput_injective_of_no_collision
#print axioms mem_commitSeen_iff_sampledInput
#print axioms commitOracle_sampledInput

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitLabels
