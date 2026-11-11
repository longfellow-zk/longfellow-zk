import LfzkV2.Current.StrandCharges

namespace LfzkV2.Current.Tests.StrandCharges

-- The concrete constructor includes the real cut, actual runtime readers,
-- role-factor normalization and both one-answer and adjacent-pair means.
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.localProof
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.localProof_budget_le
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.decoded_cover

-- Canonical tagging must preserve the stopped raw node trace, including
-- arbitrary auxiliary queries before the first commitment-context query.
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.trace_tag
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.trace_physical
#guard_msgs (drop info) in #check LfzkV2.Current.StrandCharges.cutOracle_off

/--
info: 'LfzkV2.Current.StrandCharges.localProof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandCharges.localProof

/--
info: 'LfzkV2.Current.StrandCharges.localProof_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandCharges.localProof_budget_le

/--
info: 'LfzkV2.Current.StrandCharges.trace_tag' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandCharges.trace_tag

/--
info: 'LfzkV2.Current.StrandCharges.decoded_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandCharges.decoded_cover

/--
info: 'LfzkV2.Current.StrandCharges.trace_physical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandCharges.trace_physical

end LfzkV2.Current.Tests.StrandCharges
