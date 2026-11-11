import LfzkV2.Current.StrandWindow

namespace LfzkV2.Current.Tests.StrandWindow
open TranscriptV2 TranscriptV2.Strand

-- Finite complement windows retain all PRF coordinates without requiring
-- the unrestricted byte-string address type to have a Fintype instance.
example (other : Finset OtherPoint) (H : Current.StrandWindow.Point other → Digest)
    (parent : PrfKey) (counter : Word) :
    Current.StrandWindow.oracle other H (Input.prf parent.1 parent.2 counter).encode = H (.inr (parent,counter)) :=
  Current.StrandWindow.oracle_encode other H (.inr (parent,counter))

/--
info: 'LfzkV2.Current.StrandWindow.restrict_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandWindow.restrict_run
/--
info: 'LfzkV2.Current.StrandWindow.restrict_oracle_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandWindow.restrict_oracle_run
/--
info: 'LfzkV2.Current.StrandWindow.decode_seen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandWindow.decode_seen

#print axioms Current.StrandWindow.decode_fiber

end LfzkV2.Current.Tests.StrandWindow
