import LfzkV2.Current.StrandExecution

namespace LfzkV2.Current.Tests.StrandExecution
open Application CanonicalPrefix TranscriptV2

example (raw : Bytes) (answer : Digest) :
    Current.StrandExecution.complete [(raw,answer),(raw,answer)] raw = answer := by
  simp [Current.StrandExecution.complete]

/--
info: 'LfzkV2.Current.StrandExecution.complete_agrees' depends on axioms: [propext]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandExecution.complete_agrees
/--
info: 'LfzkV2.Current.StrandExecution.decision_actual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandExecution.decision_actual
end LfzkV2.Current.Tests.StrandExecution

/--
info: 'LfzkV2.Current.StrandExecution.decoded_actual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandExecution.decoded_actual

/--
info: 'LfzkV2.Current.StrandExecution.decision_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandExecution.decision_of_trace

/--
info: 'LfzkV2.Current.StrandExecution.decoded_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandExecution.decoded_of_trace
