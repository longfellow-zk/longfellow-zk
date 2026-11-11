import LfzkV2.Current.StrandDecoder

namespace LfzkV2.Current.Tests.StrandDecoder

#guard_msgs (drop info) in #check LfzkV2.Current.StrandDecoder.oracle_eq
#guard_msgs (drop info) in #check LfzkV2.Current.StrandDecoder.decode_and_path

/--
info: 'LfzkV2.Current.StrandDecoder.oracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandDecoder.oracle_eq

/--
info: 'LfzkV2.Current.StrandDecoder.decode_and_path' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms LfzkV2.Current.StrandDecoder.decode_and_path

end LfzkV2.Current.Tests.StrandDecoder
