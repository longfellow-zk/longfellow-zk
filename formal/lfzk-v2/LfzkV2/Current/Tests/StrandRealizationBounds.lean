import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Soundness.OracleBounds

namespace LfzkV2.Current.Tests.StrandRealizationBounds
#guard_msgs (drop info) in #check Current.Soundness.OracleBounds.compiled_budget
#guard_msgs (drop info) in #check Current.Soundness.OracleBounds.linear_covered
#guard_msgs (drop info) in #check Current.Soundness.OracleBounds.seal_ratio_le
#guard_msgs (drop info) in #check Current.Soundness.OracleBounds.missing_ratio_le

-- No verifier replay budget occurs in the birthday term. With zero or one
-- original query, only the transcript positions and the final seal remain.
example (rounds : ℕ) : Current.Soundness.OracleBounds.delta 0 rounds =
    ((rounds : ℚ)+2) / 2^256 := by
  simp [Current.Soundness.OracleBounds.delta]

example (rounds : ℕ) : Current.Soundness.OracleBounds.delta 1 rounds =
    ((rounds : ℚ)+2) / 2^256 := by
  simp [Current.Soundness.OracleBounds.delta]

end LfzkV2.Current.Tests.StrandRealizationBounds

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Soundness.OracleBounds.exception_ratio_le,
  ``LfzkV2.Current.Soundness.OracleBounds.actual_collision_ratio_le]
