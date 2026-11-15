import LfzkV2.Current.StrandWindow

namespace LfzkV2.Current.Tests.StrandWindow
open TranscriptV2 TranscriptV2.Strand

-- Finite complement windows retain all PRF coordinates without requiring
-- the unrestricted byte-string address type to have a Fintype instance.

/--
info: 'LfzkV2.Current.StrandWindow.decode_seen' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms Current.StrandWindow.decode_seen

#print axioms Current.StrandWindow.decode_fiber

end LfzkV2.Current.Tests.StrandWindow
