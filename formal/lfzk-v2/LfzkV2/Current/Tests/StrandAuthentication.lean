import LfzkV2.Current.StrandAuthentication
import LfzkV2.Current.Protocol.Observation
import LfzkV2.Joint.Indexed

/-! Actual indexed authentication and final-seal replay preserve the full
verifier decision. The algebraic bridge needs only opened-column agreement. -/
namespace LfzkV2.Current.Tests.StrandAuthentication

#print axioms Merkle.Indexed.check_run
#print axioms Merkle.Indexed.check_visible
#print axioms StrandAuthentication.verify_congr
#print axioms StrandAuthentication.verify_cache_completion
#print axioms Protocol.Observation.decision_actual
#print axioms Joint.Family.verify_of_indexedAgreement

end LfzkV2.Current.Tests.StrandAuthentication
