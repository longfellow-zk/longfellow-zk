import LfzkV2.Current.StrandRealizationPath

namespace LfzkV2.Current.Tests.StrandRealization

-- The constructor uses the actual complete verifier, the exact first-
-- context cuts, and its own final-cache completion. No execution/path
-- certificate or alternative accepting predicate is an argument.
#guard_msgs (drop info) in #check Current.StrandRealization.realization
#guard_msgs (drop info) in #check Current.StrandRealization.decision_actual
#guard_msgs (drop info) in #check Current.StrandRealization.observation_law
#guard_msgs (drop info) in #check Current.StrandRealization.accepted_answers
#guard_msgs (drop info) in #check Current.StrandRealization.queryCodec
#guard_msgs (drop info) in #check Current.StrandRealization.locate_bytes
#guard_msgs (drop info) in #check Current.StrandRealization.queryCodec_label
#guard_msgs (drop info) in #check Current.StrandRealization.tag_path
#guard_msgs (drop info) in #check Current.StrandRealization.full_node_observations
#guard_msgs (drop info) in #check Current.StrandRealization.full_cut_eq

/--
info: 'LfzkV2.Current.StrandRealization.realization' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.realization

/--
info: 'LfzkV2.Current.StrandRealization.accepted_path_or_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.accepted_path_or_charge

/--
info: 'LfzkV2.Current.StrandRealization.accepted_answers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.accepted_answers

/--
info: 'LfzkV2.Current.StrandRealization.tag_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.tag_path

/--
info: 'LfzkV2.Current.StrandRealization.full_node_observations' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.full_node_observations

/--
info: 'LfzkV2.Current.StrandRealization.full_cut_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.full_cut_eq


/--
info: 'LfzkV2.Current.StrandRealization.exception_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandRealization.exception_law

end LfzkV2.Current.Tests.StrandRealization
