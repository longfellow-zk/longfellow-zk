import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Soundness.RecoveredPath

namespace LfzkV2.Current.Tests.StrandRealization

-- The shared observation uses the complete verifier and original first-context
-- cuts. Recovered paths and raw probability transport are checked separately.
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.decision_actual
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.observation_law
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.accepted_answers
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.queryCodec
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.locate_bytes
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.queryCodec_label
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.tag_path
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.full_node_observations
#guard_msgs (drop info) in #check Current.Soundness.OracleTransport.full_cut_eq

end LfzkV2.Current.Tests.StrandRealization

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Soundness.OracleTransport.accepted_path_or_charge,
  ``LfzkV2.Current.Soundness.OracleTransport.accepted_answers,
  ``LfzkV2.Current.Soundness.OracleTransport.tag_path,
  ``LfzkV2.Current.Soundness.OracleTransport.full_node_observations,
  ``LfzkV2.Current.Soundness.OracleTransport.full_cut_eq,
  ``LfzkV2.Current.Soundness.OracleTransport.exception_law]
