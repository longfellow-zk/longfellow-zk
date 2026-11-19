import TranscriptV2.StrandCoupling

namespace TranscriptV2.Tests.StrandCoupling
open TranscriptV2.StrandCoupling Merkle.RandomOracle
open scoped Classical

private def beforeNode : Tree (Point Bool Bool Bool) Bool (Bool × Bool × Bool) 4 :=
  .query (.inr (false,true)) fun first =>
    .query (.inl false) fun parent =>
      .query (.inr (parent,false)) fun second =>
        .query (.inr (parent,true)) fun repeated => .done (first,second,repeated)

private def earlyTable : SamplePoint Bool Bool → Sample Bool Bool
  | .inl _ => (false,fun _ => false)
  | .inr _ => (false,id)

-- A prequeried stream survives a later node with that same digest. Both a
-- previously read block and a previously unread block keep their original values.
example : ((eagerTree (fun (_ : Bool) digest => digest) beforeNode Cache.empty).run earlyTable).1 = (true,false,true) := by
  simp [eagerTree,beforeNode,earlyTable,Cache.empty,Cache.node,Cache.stream,Tree.run_query]

private def collision : Tree (Point Bool Bool Unit) Bool Bool 3 :=
  .query (.inl false) fun _ =>
    .query (.inl true) fun parent =>
      .query (.inr (parent,())) fun challenge => .done challenge

private def collisionTable : SamplePoint Bool Bool → Sample Bool Unit
  | .inl point => (false,fun _ => point)
  | .inr _ => (false,fun _ => true)

-- Two distinct node inputs can collide. The second node may not replace
-- the first node's stream by its own unused fresh sample.
example : ((eagerTree (fun (_ : Bool) digest => digest) collision Cache.empty).run collisionTable).1 = false := by
  simp [eagerTree,collision,collisionTable,Cache.empty,Cache.node,Cache.stream,Tree.run_query]

private def indexedCollision : Tree (Point Bool (Bool × Bool) Unit) Bool (Bool × Bool) 4 :=
  .query (.inl false) fun left =>
    .query (.inr ((false,left),())) fun first =>
      .query (.inl true) fun right =>
        .query (.inr ((true,right),())) fun second => .done (first,second)

private def indexedTable : SamplePoint Bool (Bool × Bool) → Sample Bool Unit
  | .inl position => (false,fun _ => position)
  | .inr _ => (false,fun _ => false)

-- Equal hash outputs at different positions reserve distinct PRF rows.
example : ((eagerTree Prod.mk indexedCollision Cache.empty).run indexedTable).1 = (false,true) := by
  simp [eagerTree,indexedCollision,indexedTable,Cache.empty,Cache.node,Cache.stream,Tree.run_query]

/--
info: 'TranscriptV2.StrandCoupling.eager_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandCoupling.eager_uniform

/--
info: 'TranscriptV2.StrandCoupling.eager_raw_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.StrandCoupling.eager_raw_uniform

end TranscriptV2.Tests.StrandCoupling
