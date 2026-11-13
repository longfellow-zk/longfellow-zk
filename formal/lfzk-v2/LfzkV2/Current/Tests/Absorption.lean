import LfzkV2.Current.ConcreteMetadata

namespace LfzkV2.Current.Tests.Absorption

-- The invariant is proved for arbitrary answer arrays, not merely the
-- honest challenges or accepting verifier paths.
#guard_msgs (drop info) in #check ConcreteMetadata.metadata_challengeIndependent
-- The global absorption invariant: metadata depends on the block index only,
-- so neither prover messages nor challenges can feed a derived absorbed value.
#guard_msgs (drop info) in #check ConcreteMetadata.metadata_setupOnly
#guard_msgs (drop info) in #check CanonicalRequest.ordinaryData_of_setupOnly
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
