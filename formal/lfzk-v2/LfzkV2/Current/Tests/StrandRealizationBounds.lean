import LfzkV2.Current.StrandRealizationBounds

namespace LfzkV2.Current.Tests.StrandRealizationBounds
#guard_msgs (drop info) in #check Current.StrandRealizationBounds.compiled_budget
#guard_msgs (drop info) in #check Current.StrandRealizationBounds.linear_covered
#guard_msgs (drop info) in #check Current.StrandRealizationBounds.seal_ratio_le
#guard_msgs (drop info) in #check Current.StrandRealizationBounds.missing_ratio_le

-- No verifier replay budget occurs in the birthday term. With zero or one
-- original query, only the transcript positions and the final seal remain.
example (rounds : ℕ) : Current.StrandRealizationBounds.delta 0 rounds =
    ((rounds : ℚ)+2) / 2^256 := by
  simp [Current.StrandRealizationBounds.delta]

example (rounds : ℕ) : Current.StrandRealizationBounds.delta 1 rounds =
    ((rounds : ℚ)+2) / 2^256 := by
  simp [Current.StrandRealizationBounds.delta]

/--
info: 'LfzkV2.Current.StrandRealizationBounds.exception_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealizationBounds.exception_ratio_le

/--
info: 'LfzkV2.Current.StrandRealizationBounds.actual_collision_ratio_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealizationBounds.actual_collision_ratio_le
end LfzkV2.Current.Tests.StrandRealizationBounds
