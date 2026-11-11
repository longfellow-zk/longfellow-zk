import LfzkV2.Current.StrandBackendCharges

namespace LfzkV2.Current.Tests.StrandBackendCharges
open RecursivePolygero

-- The complete response pair is tied to the actual first answer's digest.
-- Resetting unused challenge factors must never remove this link test.
example {k s n t : ℕ} {Link : Type} (P R : Joint.Participant k s n t)
    (statement : JointResponse.Statement P R) (oracle : JointResponse.Oracle P R)
    (response : Link × JointResponse.Response P R) (epsilon : ℚ) (link : Link)
    (coin : JointResponse.Coin P R) (query : LigeroFamily.QuerySet n t)
    (wrong : response.1 ≠ link) :
    JointResponse.highCharge P R statement oracle response epsilon link coin query = 0 := by
  simp only [JointResponse.highCharge,Ne.symm wrong,↓reduceIte]

#guard_msgs (drop info) in #check StrandBackendCharges.batching_decode_normalize
#guard_msgs (drop info) in #check StrandBackendCharges.opening_decode_normalize
#guard_msgs (drop info) in #check StrandBackendCharges.single_normalize
#guard_msgs (drop info) in #check StrandBackendCharges.high_normalize

/--
info: 'LfzkV2.Current.StrandBackendCharges.runtime_single_normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandBackendCharges.runtime_single_normalize

/--
info: 'LfzkV2.Current.StrandBackendCharges.runtime_single_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandBackendCharges.runtime_single_sum

/--
info: 'LfzkV2.Current.StrandBackendCharges.runtime_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandBackendCharges.runtime_pair_sum

end LfzkV2.Current.Tests.StrandBackendCharges
