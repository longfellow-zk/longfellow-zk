import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.BackendBody
import LfzkV2.Current.BackendChallenges
import LfzkV2.Current.OpeningBody

/-! One concrete runtime decoder for adaptively chosen public values. The
chosen encoding determines the path, while every statement is reconstructed
from its actual bound prefix. Requests are not unioned as fixed-public events. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveVerifier
open Application ApplicationSetup RecursivePolygero SumcheckV2
open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Proof" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

abbrev Output := RuntimeAdaptive.Output (g := g) (fields := fields) (Advice := Advice)
  (Auth := RuntimeVerifier.Authentication (g := g)) (Request := Request)

variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)

/-- Fresh message caches and the complete joint opening response are assigned
by the complete proof encoder; they are not independent correspondence inputs. -/
def encodings (request : Request) :=
  (earlier request).withProtocolWrites.withOpening (RuntimeVerifier.responses binary prime P R cfg)
    (RuntimeVerifier.encodeResponses binary prime P R cfg)

def chain := RuntimeAdaptive.chain (encodings binary prime P R cfg earlier) cfg.initialLink

omit [Fintype C] in
theorem point_eq (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) (index : ℕ) :
    (chain binary prime P R cfg earlier).point output H index =
      (((encodings binary prime P R cfg earlier output.request).chain cfg.initialLink).point output.proof H index) :=
  RuntimeAdaptive.point_eq _ _ output H index

omit [Fintype C] in
theorem finalSealPoint_eq (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) :
    (chain binary prime P R cfg earlier).finalSealPoint output H =
      ((encodings binary prime P R cfg earlier output.request).chain cfg.initialLink).finalSealPoint output.proof H :=
  point_eq binary prime P R cfg earlier output H g.roles.length

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

/-- The actual backend prefix chooses the public values. The indexed tuple
opening uses the same shared opening answer and transmitted H/Z arrays. -/
def decode (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) : Option Decoded := do
  let e := encodings binary prime P R cfg earlier output.request
  let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
  let data ← RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
    parent.point (parent.point.priorAnswers H)
  let indices := cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2
  let raw := OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings output.proof
  let claim ← OrderedOpening.decode (cfg.bindSalt (e.context output.proof)) indices raw
  pure {
    application := data.1
    statement := data.2
    claim := claim
    coin := RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2
    query := OrderedOpening.query indices }

omit [Fintype C] in
/-- All retained late values follow from the successful global reader and
actual replay; no fixed-public execution is supplied by a caller. -/
theorem decode_spec (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) (decoded : Decoded)
    (h : decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded) :
    let e := encodings binary prime P R cfg earlier output.request
    let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
    let indices := cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2
    RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      parent.point (parent.point.priorAnswers H) = some ⟨decoded.application,decoded.statement⟩ ∧
    OrderedOpening.decode (cfg.bindSalt (e.context output.proof)) indices
      (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
        cfg.binaryRows cfg.primeRows cfg.openings output.proof) = some decoded.claim ∧
    decoded.coin = RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2 ∧
    decoded.query = OrderedOpening.query indices := by
  let e := encodings binary prime P R cfg earlier output.request
  let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
  let indices := cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2
  let raw := OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings output.proof
  change Option.bind (RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      parent.point (parent.point.priorAnswers H))
    (fun data => Option.bind (OrderedOpening.decode (cfg.bindSalt (e.context output.proof)) indices raw)
      (fun claim => some ⟨data.1,data.2,claim,
        RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2,
        OrderedOpening.query indices⟩)) = some decoded at h
  cases hs : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      parent.point (parent.point.priorAnswers H) with
  | none => simp only [hs,Option.bind_none] at h; contradiction
  | some data =>
      cases hc : OrderedOpening.decode (cfg.bindSalt (e.context output.proof)) indices raw with
      | none => simp only [hs,hc,Option.bind_some,Option.bind_none] at h; contradiction
      | some claim =>
          simp only [hs,hc,Option.bind_some] at h
          cases Option.some.inj h
          exact ⟨hs,hc,rfl,rfl⟩

/-- Common arithmetic and tuple authentication checks. The complete verifier
supplies its recomputed seal, whose construction is transcript-specific. -/
def ChecksWithSeal (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (HM : Enc → Digest) (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (decoded : Decoded) (computedSeal : Digest) : Prop :=
  let e := encodings binary prime P R cfg earlier output.request
  let key := e.context output.proof
  cfg.root key = output.proof.body.commitment ∧
  output.proof.body.authentication.context = cfg.authenticationContext key ∧
  ((RuntimeVerifier.Family binary prime P R cfg).compiler cfg.openingPositive).Accepts (codec.withOracle HM)
    ((Joint.Pair.statementEquiv _ _).symm decoded.statement.statement) (cfg.root key)
    ((Joint.Pair.coinEquiv _ _).symm decoded.coin)
    ((Joint.Pair.responseEquiv _ _).symm (RuntimeVerifier.responses binary prime P R cfg output.proof))
    decoded.query decoded.claim ∧
  computedSeal = output.proof.finalSeal

/-- The earlier whole-answer transcript uses the final query's digest.
SHA strands reuse `ChecksWithSeal` with their recomputed PRF-counter-zero seal. -/
def Checks (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (HM : Enc → Digest) (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) (decoded : Decoded) : Prop :=
  ChecksWithSeal binary prime P R cfg earlier codec HM output decoded
    (H ((chain binary prime P R cfg earlier).finalSealPoint output H)).1

def verify (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (HM : Enc → Digest) (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) : Bool :=
  match decode binary prime P R cfg earlier hashPublic decodePublic draw output H with
  | none => false
  | some decoded => decide (Checks binary prime P R cfg earlier codec HM output H decoded)

omit [Fintype C] in
theorem verify_true_iff (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (HM : Enc → Digest) (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C) :
    verify binary prime P R cfg earlier hashPublic decodePublic draw codec HM output H = true ↔
      ∃ decoded, decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded ∧
        Checks binary prime P R cfg earlier codec HM output H decoded := by
  unfold verify
  cases hd : decode binary prime P R cfg earlier hashPublic decodePublic draw output H with
  | none => simp only [Bool.false_eq_true,reduceCtorEq,false_and,exists_false]
  | some decoded => simp only [decide_eq_true_eq,Option.some.injEq,exists_eq_left']

end LfzkV2.Current.RuntimeAdaptiveVerifier
