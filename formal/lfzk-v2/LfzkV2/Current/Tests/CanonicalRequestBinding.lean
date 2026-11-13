import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.Tests.ProofAudit

namespace LfzkV2.Current.Tests.CanonicalRequestBinding
run_cmd ProofAudit.standardAxioms #[``CanonicalRequest.bodyEncoding_eq,
  ``ProofBodyReplay.replay_same_body]
end LfzkV2.Current.Tests.CanonicalRequestBinding
