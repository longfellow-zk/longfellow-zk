import LfzkV2.Current.RuntimeAdaptiveVerifier

/-! One shared tuple commitment for adaptive public requests. Ordinary
verifier replay is an analysis annotation; no request or annotation is added
to the serialized proof body. The final continuation is its actual seal. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveMerkle
open Application ApplicationSetup ApplicationOracle RecursivePolygero SumcheckV2
open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "E" => RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

abbrev Annotated := RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request) ×
  Replay.State g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
    (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C

variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
private def emptyClaim : OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest where
  I := ∅
  a := fun _ => default
  pf := { nonce := fun _ => default, frontierValue := fun _ => default }

/-- Reconstruct the opening from its three inputs: the proof payload, the
bound public context and the opening answer. Transcript history and the other
cached challenges play no part in this operation. -/
def claim (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
    (context : Key) (opening : C) :
    OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest :=
  (OrderedOpening.decode (cfg.bindSalt context) (cfg.sample opening)
    (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings proof)).getD (emptyClaim binary prime P R cfg)

/-- Adapter for the generic replay annotation. The default claim only
totalizes failed decoding; acceptance still requires decoding to succeed. -/
def claimOf (out : Annotated (g := g) (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key) (C := C) (Request := Request)) :
    OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest :=
  claim binary prime P R cfg out.1.proof out.2.point.context
    (OrderedOpening.openingAnswer (g := g) cfg.fallback out.2.answers)

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)

theorem claimOf_replay (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded) :
    claimOf binary prime P R cfg (output,(M).replay output H g.roles.length) = decoded.claim := by
  have hs := RuntimeAdaptiveVerifier.decode_spec binary prime P R cfg earlier hashPublic decodePublic draw output H decoded hd
  change claimOf binary prime P R cfg
    (output,(RuntimeAdaptive.chain (E) cfg.initialLink).replay output H g.roles.length) = _
  rw [RuntimeAdaptive.replay_eq]
  unfold claimOf claim
  rw [OrderedOpening.openingAnswer_replay]
  change (OrderedOpening.decode
    (cfg.bindSalt (((E output.request).chain cfg.initialLink).point output.proof H g.roles.length).context)
    (cfg.sample (H (((E output.request).chain cfg.initialLink).point output.proof H g.openingIndex.val)).2)
    (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings output.proof)).getD (emptyClaim binary prime P R cfg) = decoded.claim
  rw [(E output.request).point_context cfg.initialLink output.proof H g.roles.length]
  rw [hs.2.1]
  rfl

end LfzkV2.Current.RuntimeAdaptiveMerkle
