import LfzkV2.Current.ZeroKnowledge.OracleProgramming
import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ProofBodyReplay

/-! Finalization for the current canonical request replay. Its ordinary
blocks depend on the proof body and strict prior answers; the final-seal
field is absent from their constructors. The complete final-seal input
contains the actual terminal authentication inside that same body. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRuntime
open CanonicalPrefix QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)

local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount

/-- This constructor uses the actual request-specific packet builder. It
does not receive the seal as an input. -/
def bodyEncoding : OracleProgramming.BodyEncoding (g := g) (fields := fields)
    (Advice := Advice) (Authentication := OpeningBody.Authentication g)
    (Context := CanonicalRequest.Key publicCount)
    (Block := QueryRuntime.Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
      (CanonicalRequest.Fresh (g := g) (fields := fields) (Advice := Advice))) (C := C) where
  context body := FingerprintPrefix.context request body.commitment
  block body := CanonicalRequest.block repr shape setup publicCount binaryRequest metadata request
    ⟨body,fun _ => 0⟩

/-- Equality to the concrete current replay is definitional: the zero seal
above is never inspected by any canonical ordinary-block constructor. -/
theorem bodyEncoding_eq :
    (bodyEncoding repr shape setup publicCount binaryRequest metadata request).encoding =
      CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request := rfl

theorem point_same_body (initial : Digest) (first second : Output)
    (same : first.body = second.body) (H : Point → Digest × C) (index : ℕ) :
    ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        first H index =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        second H index := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact congrArg _ (OracleProgramming.replay_same_body _ initial first second same H index)

def finalize (initial : Digest) (body : Body) (H : Point → Digest × C) : Output :=
  OracleProgramming.finalize (bodyEncoding repr shape setup publicCount binaryRequest metadata request)
    initial body H

/-- The complete-proof encoder queries the final seal normally after all
authentication has been fixed. No additional simulator programming occurs. -/
theorem finalize_correct (initial : Digest) (body : Body) (H : Point → Digest × C) :
    (H (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).finalSealPoint
      (finalize repr shape setup publicCount binaryRequest metadata request initial body H) H)).1 =
      (finalize repr shape setup publicCount binaryRequest metadata request initial body H).finalSeal := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact OracleProgramming.finalize_correct _ initial body H

def programAndFinalize (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) : Output × (Point → Digest × C) :=
  OracleProgramming.programAndFinalize (bodyEncoding repr shape setup publicCount binaryRequest metadata request)
    initial body H g.openingIndex answer

/-- The programmed answer is the whole direct-XOF answer: its link and all
typed samples, including coordinates the verifier does not consume. -/
theorem programmed_answer (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) :
    let result := programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer
    result.2 (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
      result.1 result.2 g.openingIndex.val) = answer := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact OracleProgramming.programAndFinalize_answer _ initial body H g.openingIndex answer

/-- Ordinary prior answers are read from the resulting programmed oracle,
and remain the base oracle's actual whole answers at the unchanged inputs. -/
theorem programmed_answer_before (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) (index : ℕ) (before : index < g.openingIndex.val) :
    let result := programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer
    result.2 (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        result.1 result.2 index) =
      H (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        (⟨body,fun _ => 0⟩ : Output) H index) := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact OracleProgramming.programAndFinalize_answer_before _ initial body H g.openingIndex answer index before

theorem programmed_final_seal (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) :
    let result := programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer
    (result.2 (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).finalSealPoint
      result.1 result.2)).1 = result.1.finalSeal := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact OracleProgramming.programAndFinalize_seal _ initial body H g.openingIndex answer

/-- Feedback at the programmed opening boundary changes no earlier input,
and computing the final seal changes none of those inputs either. -/
theorem programmed_prefix (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) (index : ℕ) (before : index ≤ g.openingIndex.val) :
    let result := programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer
    ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        result.1 result.2 index =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
        (⟨body,fun _ => 0⟩ : Output) H index := by
  rw [← bodyEncoding_eq repr shape setup publicCount binaryRequest metadata request]
  exact OracleProgramming.programAndFinalize_prefix _ initial body H g.openingIndex answer index before

@[simp] theorem programmed_body (initial : Digest) (body : Body) (H : Point → Digest × C)
    (answer : Digest × C) :
    (programAndFinalize repr shape setup publicCount binaryRequest metadata request initial body H answer).1.body = body := rfl

end LfzkV2.Current.ZeroKnowledge.OracleRuntime
