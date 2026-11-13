import LfzkV2.Current.WireOpening
import LfzkV2.Current.BackendBody

/-! Request-specific replay with the existing canonical wire packets.
The fingerprint key contains only the early request projection and root.
Later prime public inputs are written at the prime circuit's first block.
Metadata receives only the fresh message prefix and strict earlier answers;
all prover payloads are filled from the actual complete body. -/
noncomputable section
namespace LfzkV2.Current.CanonicalRequest
open CanonicalPrefix QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

abbrev Request := FingerprintPrefix.Request publicCount shape.primePublic (fields .prime)
abbrev Fresh := ProtocolWrites.Fresh g fields Advice
abbrev Base := BoundedBytes (QueryRuntime.Runtime.capacity repr shape setup publicCount)
abbrev Key := FingerprintPrefix.Key publicCount
abbrev Output := Replay.Output g fields Advice (OpeningBody.Authentication g)

/-- Public/derived writes may depend on the request and actual prefix,
including the message being bound now. No future proof fields or current
oracle answer are available through this interface. -/
abbrev Metadata := (request : Request shape publicCount) → (i : Fin g.roles.length) →
  (Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice)) →
  (Fin i.val → C) → WireBlocks.Metadata shape i

/-- Absorbed public metadata cannot depend on challenge values. Prover
messages may depend on challenges when produced, but during verifier replay
those messages are fixed by the submitted body. -/
def ChallengeIndependent (metadata : Metadata (Advice := Advice) (C := C) shape publicCount) : Prop :=
  ∀ request index writes first second,
    metadata request index writes first = metadata request index writes second

def writes (body : Current.Body g fields Advice (OpeningBody.Authentication g)) (i : Fin g.roles.length) :
    Fin (i.val+1) → Fresh (g := g) (fields := fields) (Advice := Advice) :=
  fun j => ProtocolWrites.fresh body ⟨j.val,by have := i.isLt; have := j.isLt; omega⟩

variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : Metadata (Advice := Advice) (C := C) shape publicCount)

def ordinaryData (request : Request shape publicCount)
    (body : Current.Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (past : Fin i.val → C) : WireBlocks.Data (Advice := Advice) shape i :=
  WireBlocks.fromRequest shape (binaryRequest request.publicBits) request.primeInputs i body
    (metadata request i (writes body i) past)

theorem ordinaryData_challengeIndependent
    (independent : ChallengeIndependent shape publicCount metadata)
    (request : Request shape publicCount) (body : Current.Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (first second : Fin i.val → C) :
    ordinaryData shape publicCount binaryRequest metadata request body i first =
      ordinaryData shape publicCount binaryRequest metadata request body i second := by
  unfold ordinaryData
  rw [independent request i (writes body i) first second]

/-- Index zero uses the complete initial prefix. Every later block uses
the actual role schema, with its byte base and cache constructed together. -/
def block (request : Request shape publicCount) (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (past : Fin i.val → C) :
    QueryRuntime.Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
      (Fresh (g := g) (fields := fields) (Advice := Advice)) :=
  if i.val = 0 then
    (QueryRuntime.Runtime.first repr shape setup publicCount).block
      (FingerprintPrefix.context request proof.body.commitment)
  else
    (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
      (ordinaryData shape publicCount binaryRequest metadata request proof.body i past)

/-- For a fixed request and proof body, changing sampled challenge values
cannot alter any absorbed packet. Parent digests are handled separately by
strand continuation, rather than as absorbed challenge-derived metadata. -/
theorem block_challengeIndependent
    (independent : ChallengeIndependent shape publicCount metadata)
    (request : Request shape publicCount) (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (first second : Fin i.val → C) :
    block repr shape setup publicCount binaryRequest metadata request proof i first =
      block repr shape setup publicCount binaryRequest metadata request proof i second := by
  unfold block
  split_ifs
  · rfl
  · rw [ordinaryData_challengeIndependent shape publicCount binaryRequest metadata independent]

def encoding (request : Request shape publicCount) :
    Replay.Encoding g fields Advice (OpeningBody.Authentication g) (Key publicCount)
      (QueryRuntime.Block (QueryRuntime.Runtime.capacity repr shape setup publicCount)
        (Fresh (g := g) (fields := fields) (Advice := Advice))) C where
  context proof := FingerprintPrefix.context request proof.body.commitment
  block := block repr shape setup publicCount binaryRequest metadata request

@[simp] theorem encoding_context (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice)) :
    (encoding repr shape setup publicCount binaryRequest metadata request).context proof =
      FingerprintPrefix.context request proof.body.commitment := rfl

theorem block_zero (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (hi : i.val = 0) (past : Fin i.val → C) :
    (encoding repr shape setup publicCount binaryRequest metadata request).block proof i past =
      (QueryRuntime.Runtime.first repr shape setup publicCount).block
        (FingerprintPrefix.context request proof.body.commitment) := by
  simp only [encoding,block,if_pos hi]

theorem block_pos (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (hi : i.val ≠ 0) (past : Fin i.val → C) :
    (encoding repr shape setup publicCount binaryRequest metadata request).block proof i past =
      (QueryRuntime.Runtime.ordinary repr shape setup publicCount i).block
        (ordinaryData shape publicCount binaryRequest metadata request proof.body i past) := by
  simp only [encoding,block,if_neg hi]

/-- Future prime public values are absent from the fingerprint query.
Different requests may therefore share this actual early byte prefix. -/
theorem block_zero_independent_of_prime (request : Request shape publicCount)
    (inputs : Fin shape.primePublic → fields .prime)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (hi : i.val = 0) (past : Fin i.val → C) :
    (encoding repr shape setup publicCount binaryRequest metadata {request with primeInputs := inputs}).block proof i past =
      (encoding repr shape setup publicCount binaryRequest metadata request).block proof i past := by
  rw [block_zero repr shape setup publicCount binaryRequest metadata _ proof i hi past,
    block_zero repr shape setup publicCount binaryRequest metadata request proof i hi past]
  rfl

private theorem fresh_zero (body : Current.Body g fields Advice (OpeningBody.Authentication g))
    (i : Fin g.roles.length) (hi : i.val = 0) : ProtocolWrites.fresh body i = {} := by
  have hp : i.val ≠ g.primeStart := by simp only [hi,Geometry.primeStart]; omega
  have hb : i.val ≠ g.binaryStart := by simp only [hi,Geometry.binaryStart]; omega
  have hr : g.roles.get i = .fingerprint := by simp [List.get_eq_getElem,g.roles_eq,hi]
  simp only [ProtocolWrites.fresh,hp,hb,if_false,hr,reduceCtorEq,ProtocolWrites.frontendMessages]

/-- Cache equality follows from packet construction. It is not a premise
about a separately supplied execution or semantic transcript. -/
theorem block_fresh (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (past : Fin i.val → C) :
    ((encoding repr shape setup publicCount binaryRequest metadata request).block proof i past).2 =
      ProtocolWrites.fresh proof.body i := by
  by_cases hi : i.val = 0
  · rw [block_zero repr shape setup publicCount binaryRequest metadata request proof i hi past]
    exact (fresh_zero proof.body i hi).symm
  · rw [block_pos repr shape setup publicCount binaryRequest metadata request proof i hi past]
    exact WireBlocks.fromRequest_cache shape _ _ i proof.body _

/-- Filling protocol writes again is an identity: the canonical block
already contains exactly the fresh writes of the supplied proof. -/
theorem withProtocolWrites_eq (request : Request shape publicCount) :
    (encoding repr shape setup publicCount binaryRequest metadata request).withProtocolWrites =
      encoding repr shape setup publicCount binaryRequest metadata request := by
  have hb : (encoding repr shape setup publicCount binaryRequest metadata request).withProtocolWrites.block =
      (encoding repr shape setup publicCount binaryRequest metadata request).block := by
    funext proof i past
    apply Prod.ext
    · rfl
    · exact (block_fresh repr shape setup publicCount binaryRequest metadata request proof i past).symm
  cases he : encoding repr shape setup publicCount binaryRequest metadata request with
  | mk context block =>
      change Replay.Encoding.mk context _ = Replay.Encoding.mk context block
      exact congrArg (Replay.Encoding.mk context) (by simpa only [he,Replay.Encoding.withProtocolWrites] using hb)

theorem block_opening (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (past : Fin g.openingIndex.val → C) :
    (encoding repr shape setup publicCount binaryRequest metadata request).block proof g.openingIndex past =
      WireOpening.openingWire shape repr setup publicCount
        (proof.body.binaryBackend.response,proof.body.primeBackend.response) := by
  have hi : g.openingIndex.val ≠ 0 := by
    have h := g.openingIndex_last
    have hlength := g.roles_length
    omega
  rw [block_pos repr shape setup publicCount binaryRequest metadata request proof g.openingIndex hi past]
  exact WireOpening.ordinary_fromRequest_opening shape repr setup publicCount _ _ proof.body _

/-- The complete prime-start bytes recover the late public vector of the
actual request, before the prime frontend begins consuming challenges. -/
theorem readPrimePublic_block (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (hi : i.val = g.primeStart) (past : Fin i.val → C) :
    WireBlocks.readPrimePublic repr shape (g.roles.get i)
      ((encoding repr shape setup publicCount binaryRequest metadata request).block proof i past).1.bytes =
        some request.primeInputs := by
  rw [block_pos repr shape setup publicCount binaryRequest metadata request proof i
    (by rw [hi]; exact Nat.ne_of_gt g.primeStart_pos) past]
  exact WireBlocks.readPrimePublic_fromRequest shape repr _ _ i hi proof.body _

def primeBoundary (g : Geometry) : Fin g.roles.length :=
  ⟨g.primeStart,by have := g.roles_length; dsimp only [Geometry.primeStart]; omega⟩

/-- The actual role determines the complete start-block parser. No public
vector is supplied separately to this reader. -/
def decodePrimePublic (base : Base repr shape setup publicCount) :
    Option (Fin shape.primePublic → fields .prime) :=
  WireBlocks.readPrimePublic repr shape (g.roles.get (primeBoundary g)) base.bytes

def hashPublic (key : Key publicCount) : Option (Fin publicCount → Bool) := some key.publicBits

theorem hashPublic_replay (request : Request shape publicCount) (initial : Digest)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C) (n : ℕ) :
    hashPublic publicCount
      (((encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H n).context =
        some request.publicBits := by
  rw [Replay.Encoding.point_context]
  rfl

/-- Every later replay recovers precisely the vector written at the actual
prime-start boundary. Reading the vector introduces no new oracle query. -/
theorem primePublic_replay (request : Request shape publicCount) (initial : Digest)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)
    (n : ℕ) (hn : n ≤ g.roles.length) (hstart : g.primeStart ≤ n) :
    (((encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H n).readAt
      g.primeStart (fun block => decodePrimePublic repr shape setup publicCount block.1) = some request.primeInputs := by
  change (((encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H n).readAt
    (primeBoundary g).val (fun block => decodePrimePublic repr shape setup publicCount block.1) = _
  rw [Replay.Encoding.readAt_replay _ _ _ _ _ hn (primeBoundary g) hstart]
  exact readPrimePublic_block repr shape setup publicCount binaryRequest metadata request proof _ rfl _

theorem readFirstPublic_block (request : Request shape publicCount)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (hi : i.val = 0) (past : Fin i.val → C) :
    (FingerprintPrefix.read setup publicCount
      ((encoding repr shape setup publicCount binaryRequest metadata request).block proof i past).1.bytes).map
        FingerprintPrefix.Key.publicBits = some request.publicBits := by
  rw [block_zero repr shape setup publicCount binaryRequest metadata request proof i hi past]
  exact FingerprintPrefix.public_readback setup request proof.body.commitment

section BackendOpening
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {p k s n t : ℕ} [Fact p.Prime]
variable (P : Application.FieldBackend B k s n t) (R : Application.FieldBackend (ZMod p) k s n t)
variable (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
variable (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)

omit [Algebra (ZMod 2) B] in
/-- Backend interpolation and its inverse recover the same four wire
slices. Thus the runtime's mandatory opening override is an identity for
this canonical encoder, including its response-dependent byte cache. -/
theorem withBackendOpening_eq (request : Request shape publicCount) :
    ((encoding repr shape setup publicCount binaryRequest metadata request).withProtocolWrites).withOpening
      (BackendVerifier.responses P R binary prime hrow hmask hproduct)
      (BackendVerifier.encodeResponses P R binary prime hrow hmask hproduct
        (WireOpening.openingWire shape repr setup publicCount)) =
      encoding repr shape setup publicCount binaryRequest metadata request := by
  rw [withProtocolWrites_eq]
  have hb : ((encoding repr shape setup publicCount binaryRequest metadata request).withOpening
      (BackendVerifier.responses P R binary prime hrow hmask hproduct)
      (BackendVerifier.encodeResponses P R binary prime hrow hmask hproduct
        (WireOpening.openingWire shape repr setup publicCount))).block =
      (encoding repr shape setup publicCount binaryRequest metadata request).block := by
    funext proof i past
    by_cases hi : i = g.openingIndex
    · subst i
      rw [Replay.Encoding.withOpening_block,BackendVerifier.encodeResponses_body]
      exact (block_opening repr shape setup publicCount binaryRequest metadata request proof past).symm
    · exact Replay.Encoding.withOpening_block_earlier _ _ _ proof i past hi
  cases he : encoding repr shape setup publicCount binaryRequest metadata request with
  | mk context block =>
      change Replay.Encoding.mk context _ = Replay.Encoding.mk context block
      exact congrArg (Replay.Encoding.mk context) (by simpa only [he,Replay.Encoding.withOpening] using hb)

end BackendOpening

end LfzkV2.Current.CanonicalRequest


/-! Finalization for the current canonical request replay. Its ordinary
blocks depend on the proof body and strict prior answers; the final-seal
field is absent from their constructors. The complete final-seal input
contains the actual terminal authentication inside that same body. -/
noncomputable section
namespace LfzkV2.Current.CanonicalRequest
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
def bodyEncoding : ProofBodyReplay.BodyEncoding (g := g) (fields := fields)
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
  exact congrArg _ (ProofBodyReplay.replay_same_body _ initial first second same H index)

end LfzkV2.Current.CanonicalRequest
