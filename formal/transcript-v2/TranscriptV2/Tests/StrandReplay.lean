import TranscriptV2.StrandInventory

namespace TranscriptV2.Tests.StrandReplay
open TranscriptV2.StrandCoupling Merkle.RandomOracle

private def search : Tree (Point Bool Bool Unit) Bool Unit 1 :=
  .query (.inr (false,())) fun _ => .done ()

private def replay (_ : Unit) : Tree (Point Bool Bool Unit) Bool Bool 2 :=
  .query (.inl false) fun digest =>
    .query (.inr (digest,())) fun answer => .done answer

private def answers : SamplePoint Bool Bool → Sample Bool Unit
  | .inl _ => (false,fun _ => true)
  | .inr _ => (true,fun _ => false)

-- The prover prequeries a stream. When the verifier later reaches a node
-- with that digest, the previously sampled stream must still answer false.
example : ((eagerState (fun (_ : Bool) digest => digest) (search.bind replay) Cache.empty).run answers).1.1 = false := by
  simp [eagerState,search,replay,answers,Tree.bind,Tree.weakenAdd,Cache.empty,Cache.node,Cache.stream,Tree.run_query]

/--
info: 'TranscriptV2.StrandCoupling.eagerState_comp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms eagerState_comp

#guard_msgs (drop info) in #check eagerState_recordTrace_covers
#guard_msgs (drop info) in #check eagerState_source_queries

end TranscriptV2.Tests.StrandReplay
