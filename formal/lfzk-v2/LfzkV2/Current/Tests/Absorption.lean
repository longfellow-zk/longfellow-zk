import LfzkV2.Current.ConcreteMetadata

namespace LfzkV2.Current.Tests.Absorption

-- The invariant is proved for arbitrary answer arrays, not merely the
-- honest challenges or accepting verifier paths.
#guard_msgs (drop info) in #check ConcreteMetadata.metadata_challengeIndependent
#guard_msgs (drop info) in #check CanonicalRequest.block_challengeIndependent

/--
info: 'LfzkV2.Current.ConcreteMetadata.metadata_challengeIndependent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms ConcreteMetadata.metadata_challengeIndependent

/--
info: 'LfzkV2.Current.CanonicalRequest.block_challengeIndependent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms CanonicalRequest.block_challengeIndependent

end LfzkV2.Current.Tests.Absorption
