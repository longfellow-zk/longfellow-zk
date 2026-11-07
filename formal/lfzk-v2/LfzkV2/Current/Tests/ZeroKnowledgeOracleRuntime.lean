import LfzkV2.Current.ZeroKnowledge.OracleRuntime

/-! Programming/finalization is instantiated with the concrete canonical
request encoder. Authentication stays inside the body sealed by that replay. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleRuntime
open ZeroKnowledge

variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)

example (initial : Digest) (body : Body g fields Advice (OpeningBody.Authentication g))
    (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C) (answer : Digest × C) :
    (OracleRuntime.programAndFinalize repr shape setup publicCount binaryRequest metadata request
      initial body H answer).1.body.authentication = body.authentication := rfl

#print axioms OracleRuntime.bodyEncoding_eq
#print axioms OracleRuntime.finalize_correct
#print axioms OracleRuntime.programmed_answer
#print axioms OracleRuntime.programmed_final_seal

end LfzkV2.Current.Tests.ZeroKnowledgeOracleRuntime
