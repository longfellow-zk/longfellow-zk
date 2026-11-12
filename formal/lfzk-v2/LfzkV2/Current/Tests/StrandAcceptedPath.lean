import TranscriptV2.Composition
import LfzkV2.Current.StrandReplay
import LfzkV2.Current.StrandAcceptedPath

namespace LfzkV2.Current.Tests.StrandAcceptedPath
open Merkle.RandomOracle TranscriptV2

#guard_msgs (drop info) in #check StrandReplay.path_or_charge
#guard_msgs (drop info) in #check StrandReplay.node_stream
#guard_msgs (drop info) in #check StrandAcceptedPath.value_point

/--
info: 'LfzkV2.Current.StrandAcceptedPath.value_history' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandAcceptedPath.value_history

-- Even with no ordinary rounds, the path includes the final node. A
-- zero-query search cannot acquire a path allowance from verifier replay.
example (H : Unit → Bool × Bool) :
    ¬Composition.PathQueries (rounds := 0) (.done () : Tree Unit (Bool × Bool) Unit 0) H (fun _ => ()) := by
  intro path
  have queried := path.queried 0 le_rfl
  exact Finset.notMem_empty () queried

end LfzkV2.Current.Tests.StrandAcceptedPath
