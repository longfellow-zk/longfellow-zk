import LfzkV2.Current.ApplicationPrefix
import LfzkV2.Current.BackendChallenges
import LfzkV2.Current.BackendPath
import LfzkV2.Current.OpeningBody

/-! A runtime verifier assembled from the actual proof messages. Public setup
contains the trusted hash/signature circuits, field representations, challenge
decoders and opening packet encoder. The application system, affine
rows, payloads and opening are reconstructed by the adaptive decoder; no execution certificate or
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

abbrev System := Application.System B (Fin binary.degree) (Fin binary.words) binary.Slot binary.Pad
  prime.Other (Fin prime.pads) binary.Original prime.Original C C Adapter.Mdoc.primeOrder
  shared maskBits Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound

/-- The successful runtime decode carries the constructed affine statement
and the actual query-indexed tuple opening. It contains no execution proof. -/
structure Decoded where
  application : System binary prime (C := C)
  statement : StatementData application (first binary prime P R cfg) (second binary prime P R cfg)
  claim : OpeningClaim n Salt (Family binary prime P R cfg).Leaf Digest
  coin : JointResponse.Coin (first binary prime P R cfg).participant (second binary prime P R cfg).participant
  query : LigeroFamily.QuerySet n t

/-- The total compiler has a fixed algebraic fallback, not a fabricated
certified application. No accepted decoding can select this branch. -/
def zeroStatement : JointResponse.Statement (first binary prime P R cfg).participant (second binary prime P R cfg).participant :=
  (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)


def queryDecoder (answer : C) : LigeroFamily.QuerySet n t := OrderedOpening.query (cfg.sample answer)


def wireResponses (response : JointResponse.Response (first binary prime P R cfg).participant (second binary prime P R cfg).participant) :
    Response g (fields .binary) × Response g (fields .prime) :=
  (BackendVerifier.responsesEquiv (first binary prime P R cfg) (second binary prime P R cfg) cfg.binaryField cfg.primeField cfg.rowDimension cfg.maskingDegree
    (RuntimeVerifier.productFits binary prime P R cfg)).symm response


end LfzkV2.Current.RuntimeVerifier
