import TranscriptV2.FreshRenaming

namespace TranscriptV2.Tests.FreshRenaming
open TranscriptV2.FreshOracle Merkle.RandomOracle
open scoped Classical

private def repeated : Tree Bool Bool Bool 2 :=
  .query false fun first => .query false fun second => .done (first == second)

-- An online label may depend on state, but changing that state cannot make
-- an already answered raw query fresh again.
example (H : Bool × Bool → Bool) :
    ((rename (fun state point => (state,point)) (fun state _ _ => !state)
      repeated ∅ (fun _ => false) false).run H).1 = true := by
  simp [rename,repeated,Tree.run_query,Tree.run_weaken]

example :
    mean (fun result : Bool => if result then 1 else 0)
      (memoize repeated ∅ (fun _ => false)) = 1 := by
  simp [memoize,rename,repeated,mean,mean_weaken]

/--
info: 'TranscriptV2.FreshOracle.rename_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms TranscriptV2.FreshOracle.rename_uniform

end TranscriptV2.Tests.FreshRenaming
