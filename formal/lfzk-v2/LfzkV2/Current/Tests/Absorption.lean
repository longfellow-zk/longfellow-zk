import LfzkV2.Current.MdocRuntime

namespace LfzkV2.Current.Tests.Absorption

-- The global absorption invariant: the deployed format absorbs no
-- per-boundary metadata, so neither prover messages nor challenges can feed
-- a derived absorbed value. Every setup constant is in node 0.
#guard_msgs (drop info) in #check MdocRuntime.metadata_setupOnly
#guard_msgs (drop info) in #check TaggedFormat.fromBody_cache

/--
info: 'LfzkV2.Current.MdocRuntime.metadata_setupOnly' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms MdocRuntime.metadata_setupOnly

end LfzkV2.Current.Tests.Absorption
