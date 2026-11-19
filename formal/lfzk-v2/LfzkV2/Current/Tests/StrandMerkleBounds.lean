import LfzkV2.Current.StrandMerkleBounds

/-! Audit the actual reader/window instantiation separately from the
generic one-path counting theorem. No execution or oracle-independence
certificate is an axiom of these results. -/
namespace LfzkV2.Current.Tests.StrandMerkleBounds

#print axioms StrandMerkleBounds.cut_subset
#print axioms StrandMerkleBounds.selected_off
#print axioms StrandMerkleBounds.merkle_fiber
#print axioms StrandMerkleBounds.freshHit_ratio_le
#print axioms StrandMerkleBounds.selected_spec
#print axioms Soundness.OracleTransport.observation_law
#print axioms Soundness.OracleTransport.rawView_actual
#print axioms Soundness.OracleTransport.observe_cut
#print axioms StrandMerkleBounds.path_represented
#print axioms StrandMerkleBounds.accepted_cover
#print axioms StrandMerkleMissingQueries.disagreement_restricted_cover
#print axioms Merkle.Indexed.pathInput_visible

end LfzkV2.Current.Tests.StrandMerkleBounds
