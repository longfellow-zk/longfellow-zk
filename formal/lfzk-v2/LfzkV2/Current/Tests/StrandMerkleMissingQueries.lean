import LfzkV2.Current.StrandMerkleMissingQueries
import LfzkV2.Current.MerkleWireCodec

/-! Axiom audit of the one-path probability bound and its concrete byte
separation law. The actual PRF-only selector remains a separate obligation. -/
namespace LfzkV2.Current.Tests.StrandMerkleMissingQueries

#print axioms Merkle.Indexed.nodeInput_off
#print axioms Merkle.Indexed.disagreement_hit
#print axioms MerkleWireCodec.separated
#print axioms TranscriptV2.UnqueriedAnswer.density_le
#print axioms LfzkV2.Current.StrandMerkleMissingQueries.chosen_off
#print axioms LfzkV2.Current.StrandMerkleMissingQueries.disagreement_restricted_cover
#print axioms TranscriptV2.UnqueriedAnswer.partial_density_le
#print axioms LfzkV2.Current.StrandMerkleMissingQueries.restricted_any_hit_density_le

end LfzkV2.Current.Tests.StrandMerkleMissingQueries
