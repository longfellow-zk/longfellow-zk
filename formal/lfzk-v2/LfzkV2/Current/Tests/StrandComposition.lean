import LfzkV2.Current.StrandComposition

namespace LfzkV2.Current.Tests.StrandComposition
open LfzkV2.Current.StrandComposition TranscriptV2 Merkle.RandomOracle Bcs.FiniteProbability
open scoped Classical

private def adaptive : Tree Bool (Bool × Bool) Bool 2 :=
  .query false fun first => .query first.2 fun second => .done second.1

-- Even an adaptive next address ignores analysis-only padding.
example (H : Bool → Bool × (Bool × Bool)) :
    ((LfzkV2.Current.StrandComposition.pad (Extra := Bool) adaptive).run H).1 = (adaptive.run (drop H)).1 :=
  (pad_run (Extra := Bool) adaptive H).1

example (event : (Bool → Bool × Bool) → Prop) :
    density (fun H : Bool → Bool × (Bool × Bool) => event (drop H)) = density event :=
  pad_law event

-- The inverse coordinate map retains the full table, rather than merely
-- its scalar marginal or the answer at the selected extraction point.
example (H : Bool → Bool × (Bool × Bool)) :
    (StrandSampling.oracleEquiv (Link := Bool) (fun _ : Bool => Equiv.refl (Bool × Bool))).symm
      ((StrandSampling.oracleEquiv (Link := Bool) (fun _ : Bool => Equiv.refl (Bool × Bool))) H) = H :=
  Equiv.symm_apply_apply _ H

/--
info: 'LfzkV2.Current.StrandComposition.padded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms padded

/--
info: 'LfzkV2.Current.StrandComposition.atResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms atResidual

/--
info: 'LfzkV2.Current.StrandComposition.observation_average' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms observation_average

end LfzkV2.Current.Tests.StrandComposition

#guard_msgs (drop info) in #check LfzkV2.Current.StrandComposition.coordinates_seen

/--
info: 'LfzkV2.Current.StrandComposition.coordinates_seen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandComposition.coordinates_seen

#guard_msgs (drop info) in #check LfzkV2.Current.StrandComposition.coordinates_charge

/--
info: 'LfzkV2.Current.StrandComposition.coordinates_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandComposition.coordinates_charge


#guard_msgs (drop info) in #check LfzkV2.Current.StrandComposition.event_average
/--
info: 'LfzkV2.Current.StrandComposition.event_average' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandComposition.event_average
