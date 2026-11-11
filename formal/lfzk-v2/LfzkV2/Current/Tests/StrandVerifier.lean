import LfzkV2.Current.StrandVerifier

namespace LfzkV2.Current.Tests.StrandVerifier

-- The complete verifier reuses the actual application and tuple decoder,
-- rejects both a failed physical sampler and an incorrect stored seal,
-- and finalizes the actual canonical proof body.
#guard_msgs (drop info) in #check StrandVerifier.verify_true_iff
#guard_msgs (drop info) in #check StrandVerifier.finalSeal_body
#guard_msgs (drop info) in #check StrandVerifier.reject_failed_sample
#guard_msgs (drop info) in #check StrandVerifier.reject_final_seal

/--
info: 'LfzkV2.Current.StrandVerifier.accepted_seal_query' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandVerifier.accepted_seal_query

end LfzkV2.Current.Tests.StrandVerifier
