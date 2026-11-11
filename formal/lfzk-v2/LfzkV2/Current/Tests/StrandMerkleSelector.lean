import LfzkV2.Current.StrandMerkleSelector

/-! The actual indexed ordered opening supplies one disagreeing path,
and changing any Merkle answer cannot change the selector. -/
namespace LfzkV2.Current.Tests.StrandMerkleSelector

#print axioms StrandMerkleSelector.select_spec
#print axioms StrandMerkleSelector.read_merkle_off
#print axioms StrandMerkleSelector.recordedSelect_off
#print axioms StrandMerkleSelector.recordedSelect_spec

end LfzkV2.Current.Tests.StrandMerkleSelector
