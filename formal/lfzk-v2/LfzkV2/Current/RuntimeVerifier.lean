import LfzkV2.Current.ApplicationPrefix
import LfzkV2.Current.BackendChallenges
import LfzkV2.Current.BackendPath
import LfzkV2.Current.OpeningBody

/-! A runtime verifier assembled from the actual proof messages. Public setup
contains the trusted hash/signature circuits, field representations, challenge
decoders and deterministic bind-only framing. The application system, affine
rows, payloads and opening are reconstructed here; no execution certificate or
semantic acceptance checker is a parameter. `Base × Fresh` is a logical
view of each block; its byte encoder may interleave derived binds and fresh
writes in the actual role-specific order, without serializing extra tags. -/
noncomputable section
namespace LfzkV2.Current.RuntimeVerifier
open Application ApplicationSetup RecursivePolygero SumcheckV2
open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B k s n t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) k s n t)

abbrev Authentication := OpeningBody.Authentication g
abbrev Block := Base × ProtocolWrites.Fresh g fields Advice
abbrev Output := Replay.Output g fields Advice (Authentication (g := g))
abbrev Point := Replay.Point g fields Advice (Authentication (g := g)) Key
  (Block (g := g) (fields := fields) (Advice := Advice) (Base := Base))

/-- These parameters fix public algebra and representation, not a decoded
system or a claim that an adversarial proof follows the verifier. Uniformity
of challenge decoders belongs to the stated ideal-XOF model. -/
structure Public where
  card : Fintype.card B = Adapter.Mdoc.binaryOrder
  /-- Polynomial-basis x, before the fixed adapter exponent is applied. -/
  polynomialX : Bˣ
  quotientBound : 2^adviceBits ≤ Adapter.Mdoc.quotientBound
  packingDegree : g.packingDegree = binary.degree
  binaryField : fields .binary ≃ B
  primeField : fields .prime ≃ ZMod Adapter.Mdoc.primeOrder
  binaryDecode : C → ℕ → B
  binaryNonzero : C → Linear.TerminalSampling.Nonzero B
  primeDecode : C → ℕ → ZMod Adapter.Mdoc.primeOrder
  primeNonzero : C → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder)
  conversion : C → Fin 2 → Linear.TerminalSampling.Nonzero (ZMod Adapter.Mdoc.primeOrder)
  fingerprintBinary : C → WitnessSelection.Coins B binary.Original
  fingerprintPrime : C → WitnessSelection.Coins (ZMod Adapter.Mdoc.primeOrder) prime.Original
  advice : Advice → Option (Fin 2 → Fin adviceBits → Bool)
  fallback : C
  countBinary : ℕ
  countPrime : ℕ
  rowDimension : g.rowDimension = k
  maskingDegree : g.maskingDegree = s
  binaryRows : g.dataRows .binary = P.backend.nw
  primeRows : g.dataRows .prime = R.backend.nw
  openings : g.openings = t
  columns : g.columns = n
  openingPositive : 0 < t
  context : Digest → Key
  bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
    (Fin i.val → C) → Base
  openingBase : Response g (fields .binary) × Response g (fields .prime) → Base
  initialLink : Digest
  root : Key → Digest
  authenticationContext : Key → Digest
  bindSalt : Key → Fin n → MerkleNonce → Salt
  sample : C → (Fin t ↪ Fin n)

variable (cfg : Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))

include cfg in
omit [DecidableEq B] in
/-- The existing shared geometry validates the interpolation domain size. -/
theorem productFits : 2*k ≤ n := by
  simpa only [cfg.rowDimension,cfg.columns] using g.productFits

include cfg in
omit [DecidableEq B] in
theorem rowPositive : 0 < k := by
  have h := g.openings_lt
  rw [cfg.rowDimension] at h
  omega

/-- Field evaluations in the one batching answer, in participant order. -/
abbrev RawSamples :=
  (Fin (BackendChallenges.size cfg.countBinary P.backend.nw P.backend.s) → B) ×
    (Fin (BackendChallenges.size cfg.countPrime R.backend.nw R.backend.s) →
      ZMod Adapter.Mdoc.primeOrder)

/-- Fix the runtime batching codec from raw typed XOF samples. The reader
finishes the binary block before the prime block; this constructor fixes
its equation indices, physical row order and evaluation interpolation. -/
def batchingDecoder (draw : C → RawSamples binary prime P R cfg) : C →
    JointResponse.Coin (P.indexed cfg.countBinary).participant (R.indexed cfg.countPrime).participant :=
  fun answer => BackendChallenges.pairEquiv P R cfg.countBinary cfg.countPrime
    (rowPositive binary prime P R cfg) (draw answer)

abbrev first := P.indexed cfg.countBinary
abbrev second := R.indexed cfg.countPrime
abbrev Family := Joint.Pair.family (first binary prime P R cfg).participant (second binary prime P R cfg).participant

/-- The opening boundary contains both complete H/Z arrays. Its base is
the encoding of those same writes, and its fresh component is their cache. -/
def openingWire (responses : Response g (fields .binary) × Response g (fields .prime)) :
    Block (g := g) (fields := fields) (Advice := Advice) (Base := Base) :=
  (cfg.openingBase responses,{ responses := some responses })

def responses (proof : Output (g := g) (fields := fields) (Advice := Advice)) :=
  BackendVerifier.responses (first binary prime P R cfg) (second binary prime P R cfg) cfg.binaryField cfg.primeField
    cfg.rowDimension cfg.maskingDegree (productFits binary prime P R cfg) proof

def encodeResponses := BackendVerifier.encodeResponses (first binary prime P R cfg) (second binary prime P R cfg)
  cfg.binaryField cfg.primeField cfg.rowDimension cfg.maskingDegree (productFits binary prime P R cfg) (openingWire binary prime P R cfg)

omit [DecidableEq B] in
theorem openingWire_injective : Function.Injective (openingWire binary prime P R cfg) := by
  intro first second h
  exact Option.some.inj (congrArg (fun block => block.2.responses) h)

/-- Both participant payloads are retained by the boundary encoder. -/
theorem encodeResponses_injective : Function.Injective (encodeResponses binary prime P R cfg) :=
  BackendVerifier.encodeResponses_injective (first binary prime P R cfg) (second binary prime P R cfg)
    cfg.binaryField cfg.primeField cfg.rowDimension cfg.maskingDegree (productFits binary prime P R cfg)
    (openingWire binary prime P R cfg) (openingWire_injective binary prime P R cfg)

/-- Bind-only framing receives only public data, the actual message prefix
through this boundary, and strict prior challenges. It cannot read a future
proof field. The fresh component is filled by `withProtocolWrites` below. -/
def framing : Replay.Encoding g fields Advice (Authentication (g := g)) Key
    (Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C where
  context proof := cfg.context proof.body.commitment
  block proof i past :=
    (cfg.bindOnly i (fun j => ProtocolWrites.fresh proof.body ⟨j.val,by
      have hi := i.isLt
      have hj := j.isLt
      omega⟩) past,{})

/-- Earlier payloads are assigned to their actual protocol boundaries. The
opening override only fixes its complete response-pair framing. -/
def encoding := (framing binary prime P R cfg).withProtocolWrites.withOpening
  (responses binary prime P R cfg) (encodeResponses binary prime P R cfg)

@[simp] theorem encoding_context
    (proof : Output (g := g) (fields := fields) (Advice := Advice)) :
    (encoding binary prime P R cfg).context proof = cfg.context proof.body.commitment := rfl

theorem encoding_opening
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (past : Fin g.openingIndex.val → C) :
    (encoding binary prime P R cfg).block proof g.openingIndex past =
      encodeResponses binary prime P R cfg (responses binary prime P R cfg proof) := by
  simp only [encoding,Replay.Encoding.withOpening_block]

/-- Every earlier fresh payload comes from the actual complete proof body. -/
theorem encoding_fresh_before
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (i : Fin g.roles.length) (past : Fin i.val → C) (hi : i ≠ g.openingIndex) :
    ((encoding binary prime P R cfg).block proof i past).2 = ProtocolWrites.fresh proof.body i := by
  rw [encoding,Replay.Encoding.withOpening_block_earlier _ _ _ _ _ _ hi]
  rfl

abbrev System := Application.System B (Fin binary.degree) (Fin binary.words) binary.Slot binary.Pad
  prime.Other (Fin prime.pads) binary.Original prime.Original C C Adapter.Mdoc.primeOrder
  shared maskBits Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound

/-- Read only the strict batching prefix, including both early fingerprint
responses. Equation indices and physical addresses are constructed by the
compiler after their numerical checks; they are never supplied as witnesses. -/
def statementAt (point : Point (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key)) (past : Fin point.rank → C) :
    Option (Σ A : System binary prime (C := C),
      StatementData A (first binary prime P R cfg) (second binary prime P R cfg)) := do
  let A ← ApplicationPrefix.decodeChecked binary prime cfg.card cfg.polynomialX
    cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
    cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero
    cfg.conversion cfg.advice cfg.fallback point past
  let layout ← StatementCompiler.addresses P R binary.cells prime.remaining prime.pads
  let fingerprint ← ApplicationPrefix.strictAnswer point past 0
  let targets ← point.readAt g.primeStart (fun block => block.2.fingerprints)
  let data ← StatementCompiler.compile P R A layout cfg.countBinary cfg.countPrime
    (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint)
    (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
    (cfg.primeField targets.2.1,cfg.primeField targets.2.2)
  pure ⟨A,data⟩


/-- At a fixed query preimage the whole affine statement reads only strict
ancestors. Its own challenge answer is unavailable to the compiler. -/
theorem statementAt_off (point : Point (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key))
    (H H' : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') :
    statementAt binary prime P R cfg point (point.priorAnswers H) =
      statementAt binary prime P R cfg point (point.priorAnswers H') := by
  rw [point.priorAnswers_off h]

/-- A successful affine-statement reader exposes the actual application
parse, physical-capacity checks and two bound fingerprint responses. -/
theorem statementAt_spec (point : Point (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key)) (past : Fin point.rank → C)
    (data : Σ A : System binary prime (C := C),
      StatementData A (first binary prime P R cfg) (second binary prime P R cfg))
    (h : statementAt binary prime P R cfg point past = some data) :
    ApplicationPrefix.decodeChecked binary prime cfg.card cfg.polynomialX
      cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
      cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero
      cfg.conversion cfg.advice cfg.fallback point past = some data.1 ∧
    ∃ layout fingerprint targets,
      StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout ∧
      ApplicationPrefix.strictAnswer point past 0 = some fingerprint ∧
      point.readAt g.primeStart (fun block => block.2.fingerprints) = some targets ∧
      StatementCompiler.compile P R data.1 layout cfg.countBinary cfg.countPrime
        (cfg.fingerprintBinary fingerprint) (cfg.fingerprintPrime fingerprint)
        (cfg.binaryField targets.1.1,cfg.binaryField targets.1.2)
        (cfg.primeField targets.2.1,cfg.primeField targets.2.2) = some data.2 := by
  simp only [statementAt,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
  obtain ⟨A,hA,layout,hlayout,fingerprint,hfingerprint,targets,htargets,statement,hstatement,hresult⟩ := h
  cases Option.some.inj hresult
  exact ⟨hA,layout,fingerprint,targets,hlayout,hfingerprint,htargets,hstatement⟩

/-- The successful runtime decode carries the constructed affine statement
and the actual query-indexed tuple opening. It contains no execution proof. -/
structure Decoded where
  application : System binary prime (C := C)
  statement : StatementData application (first binary prime P R cfg) (second binary prime P R cfg)
  claim : OpeningClaim n Salt (Family binary prime P R cfg).Leaf Digest
  coin : JointResponse.Coin (first binary prime P R cfg).participant (second binary prime P R cfg).participant
  query : LigeroFamily.QuerySet n t

variable [Inhabited (Family binary prime P R cfg).Leaf]

/-- Decode all protocol data using the ordinary replay. The two fields use
one opening answer; the proof contains rows and authentication, not indices.
The only batching-sampler input is raw field draws. Interpolation and physical
row ordering are fixed here rather than supplied as a coin decoder. -/
def decode (draw : C → RawSamples binary prime P R cfg)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C) :
    Option (Decoded binary prime P R cfg) := do
  let parent := BackendPath.parent (encoding binary prime P R cfg) cfg.initialLink proof H g.batchingIndex
  let data ← statementAt binary prime P R cfg parent.point (parent.point.priorAnswers H)
  let answer := (H (((encoding binary prime P R cfg).chain cfg.initialLink).point proof H g.openingIndex.val)).2
  let indices := cfg.sample answer
  let raw := OpeningBody.raw (first binary prime P R cfg).participant (second binary prime P R cfg).participant
    cfg.binaryField cfg.primeField cfg.binaryRows cfg.primeRows cfg.openings proof
  let claim ← OrderedOpening.decode (cfg.bindSalt ((encoding binary prime P R cfg).context proof)) indices raw
  pure {
    application := data.1
    statement := data.2
    claim := claim
    coin := batchingDecoder binary prime P R cfg draw (H parent.point).2
    query := OrderedOpening.query indices }

/-- Every retained value is tied to its successful concrete reader. This
is the handoff used to construct an execution after verifier acceptance. -/
theorem decode_spec
    (draw : C → RawSamples binary prime P R cfg)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C)
    (decoded : Decoded binary prime P R cfg)
    (h : decode binary prime P R cfg draw proof H = some decoded) :
    let parent := BackendPath.parent (encoding binary prime P R cfg) cfg.initialLink proof H g.batchingIndex
    let indices := cfg.sample (H (((encoding binary prime P R cfg).chain cfg.initialLink).point
      proof H g.openingIndex.val)).2
    statementAt binary prime P R cfg parent.point (parent.point.priorAnswers H) =
      some ⟨decoded.application,decoded.statement⟩ ∧
    OrderedOpening.decode (cfg.bindSalt ((encoding binary prime P R cfg).context proof)) indices
      (OpeningBody.raw (first binary prime P R cfg).participant (second binary prime P R cfg).participant
        cfg.binaryField cfg.primeField cfg.binaryRows cfg.primeRows cfg.openings proof) = some decoded.claim ∧
    decoded.coin = batchingDecoder binary prime P R cfg draw (H parent.point).2 ∧
    decoded.query = OrderedOpening.query indices := by
  let parent := BackendPath.parent (encoding binary prime P R cfg) cfg.initialLink proof H g.batchingIndex
  let indices := cfg.sample (H (((encoding binary prime P R cfg).chain cfg.initialLink).point
    proof H g.openingIndex.val)).2
  let raw := OpeningBody.raw (first binary prime P R cfg).participant (second binary prime P R cfg).participant
    cfg.binaryField cfg.primeField cfg.binaryRows cfg.primeRows cfg.openings proof
  change Option.bind (statementAt binary prime P R cfg parent.point (parent.point.priorAnswers H))
    (fun data => Option.bind (OrderedOpening.decode (cfg.bindSalt ((encoding binary prime P R cfg).context proof)) indices raw)
      (fun claim => some ⟨data.1,data.2,claim,batchingDecoder binary prime P R cfg draw (H parent.point).2,
        OrderedOpening.query indices⟩)) = some decoded at h
  cases hs : statementAt binary prime P R cfg parent.point (parent.point.priorAnswers H) with
  | none => simp only [hs,Option.bind_none] at h; contradiction
  | some data =>
      cases hc : OrderedOpening.decode (cfg.bindSalt ((encoding binary prime P R cfg).context proof)) indices raw with
      | none => simp only [hs,hc,Option.bind_some,Option.bind_none] at h; contradiction
      | some claim =>
          simp only [hs,hc,Option.bind_some] at h
          cases Option.some.inj h
          exact ⟨hs,hc,rfl,rfl⟩

/-- The actual verifier checks one jointly authenticated opening against the
constructed statement, both transmitted H/Z arrays, the shared sample and
the complete-body final seal. The two context checks reject malformed roots. -/
def Checks
    (codec : Codec Salt (Family binary prime P R cfg).Leaf Digest Enc) (HM : Enc → Digest)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C)
    (decoded : Decoded binary prime P R cfg) : Prop :=
  let key := (encoding binary prime P R cfg).context proof
  cfg.root key = proof.body.commitment ∧
  proof.body.authentication.context = cfg.authenticationContext key ∧
  ((Family binary prime P R cfg).compiler cfg.openingPositive).Accepts (codec.withOracle HM)
    ((Joint.Pair.statementEquiv _ _).symm decoded.statement.statement) (cfg.root key)
    ((Joint.Pair.coinEquiv _ _).symm decoded.coin)
    ((Joint.Pair.responseEquiv _ _).symm (responses binary prime P R cfg proof)) decoded.query decoded.claim ∧
  (H (((encoding binary prime P R cfg).chain cfg.initialLink).finalSealPoint proof H)).1 = proof.finalSeal

/-- This mathematical runtime model rejects malformed decoding before
checking authentication and arithmetic. Its classical decision operation is
not a claim about Lean VM execution. The caller supplies neither a System
nor an Execution certificate. -/
def verify
    (draw : C → RawSamples binary prime P R cfg)
    (codec : Codec Salt (Family binary prime P R cfg).Leaf Digest Enc) (HM : Enc → Digest)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C) : Bool :=
  match decode binary prime P R cfg draw proof H with
  | none => false
  | some decoded => decide (Checks binary prime P R cfg codec HM proof H decoded)

/-- Acceptance supplies the actual successful decoder branch and every
runtime check. Subsequent soundness proofs reconstruct their execution from
these values, rather than assuming a supplied execution certificate. -/
theorem verify_true_iff
    (draw : C → RawSamples binary prime P R cfg)
    (codec : Codec Salt (Family binary prime P R cfg).Leaf Digest Enc) (HM : Enc → Digest)
    (proof : Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C) :
    verify binary prime P R cfg draw codec HM proof H = true ↔
      ∃ decoded, decode binary prime P R cfg draw proof H = some decoded ∧
        Checks binary prime P R cfg codec HM proof H decoded := by
  unfold verify
  cases hd : decode binary prime P R cfg draw proof H with
  | none => simp only [Bool.false_eq_true,reduceCtorEq,false_and,exists_false]
  | some decoded => simp only [decide_eq_true_eq,Option.some.injEq,exists_eq_left']

end LfzkV2.Current.RuntimeVerifier
