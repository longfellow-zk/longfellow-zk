import LfzkV2.Current.StrandVerifier

namespace LfzkV2.Current.Tests.StrandVerifier

-- The complete verifier reuses the actual application and tuple decoder,
-- rejects both a failed physical sampler and an incorrect stored seal,
-- and finalizes the actual canonical proof body.
#guard_msgs (drop info) in #check StrandVerifier.verify_true_iff

end LfzkV2.Current.Tests.StrandVerifier
