import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
import LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody

/-! Check the actual proof constructor, both field encoders, honest dummy
authentication and normal finalization. In particular the complete public
algorithm accepts no witness, backend satisfaction or acceptance argument. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeCompleteVerifier
open ZeroKnowledge

#check @CompleteCanonicalVerifier.complete
#print axioms CompleteOpening.decode_raw
#print axioms CompleteOpening.claim_accepts
#print axioms CompleteOpening.raw_frontier_bound
#print axioms CompleteBody.raw_fill
#print axioms CompleteBackend.compiled_verifies
#print axioms CompleteFrontendBody.binary_decode
#print axioms CompleteFrontendBody.prime_decode
#print axioms CompleteVerifier.simulatedBody_responses
#print axioms CompleteVerifier.simulatedBody_raw
#print axioms CompleteProgrammed.prior_answers
#print axioms CompleteProgrammedVerifier.accepts
#print axioms CompleteTerminal.replay_before
#print axioms CompleteCanonicalVerifier.filled_batchingPoint
#print axioms CompleteCanonicalVerifier.complete_success_accepts

end LfzkV2.Current.Tests.ZeroKnowledgeCompleteVerifier
