import LfzkV2.Current.StrandCutObservation

namespace LfzkV2.Current.Tests.StrandCutObservation
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand TranscriptV2.StrandCoupling

-- PRF reads and repeated node inputs reveal no new authentication input.
example {P T Key : Type} [DecidableEq P] (schema : History.Codec T) (bytes : P → Framing.Bytes)
    (context : T → Key) (key : Key) (raw : P) (digest : Digest) (counter : Word)
    (answer : Digest) (id : Word) (past : List Entry) :
    Current.StrandCutObservation.scan schema bytes context key (fun _ => some digest) past
      [(.inr ((id,digest),counter),answer),(.inl raw,answer),(.inl raw,answer)] = [] := rfl

/--
info: 'LfzkV2.Current.StrandCutObservation.scan_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandCutObservation.scan_eq_trace

/--
info: 'LfzkV2.Current.StrandCutObservation.recorded_scan_eq_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandCutObservation.recorded_scan_eq_trace

/--
info: 'LfzkV2.Current.StrandCutObservation.completion_cut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandCutObservation.completion_cut

/--
info: 'LfzkV2.Current.StrandCutObservation.completion_observation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandCutObservation.completion_observation


/--
info: 'LfzkV2.Current.StrandCutObservation.completion_law' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandCutObservation.completion_law

end LfzkV2.Current.Tests.StrandCutObservation
