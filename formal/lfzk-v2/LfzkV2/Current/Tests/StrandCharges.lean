import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Soundness.LocalCharges

namespace LfzkV2.Current.Tests.StrandCharges

-- The concrete constructor includes the real cut, actual runtime readers,
-- role-factor normalization and both one-answer and adjacent-pair means.
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.localProof
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.localProof_budget_le
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.decoded_cover

-- Canonical tagging must preserve the stopped raw node trace, including
-- arbitrary auxiliary queries before the first commitment-context query.
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.trace_tag
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.trace_physical
#guard_msgs (drop info) in #check LfzkV2.Current.Soundness.LocalCharges.cutOracle_off

end LfzkV2.Current.Tests.StrandCharges

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Soundness.LocalCharges.localProof,
  ``LfzkV2.Current.Soundness.LocalCharges.localProof_budget_le,
  ``LfzkV2.Current.Soundness.LocalCharges.trace_tag,
  ``LfzkV2.Current.Soundness.LocalCharges.decoded_cover,
  ``LfzkV2.Current.Soundness.LocalCharges.trace_physical]
