import LfzkV2.Current.RuntimeAdaptiveVerifier

noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveVerifier
open Application ApplicationSetup RecursivePolygero SumcheckV2
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
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Proof" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg

variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]


/-- Constructor direction of the actual decoder. Both premises are the
literal runtime subcomputations, so callers can prove them from an honest
frontend and its encoded opening without unfolding the entire decoder. -/
theorem decode_of_parts (output : Output (g := g) (fields := fields) (Advice := Advice) (Request := Request))
    (H : Point → Digest × C)
    (data : Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second)
    (claim : OpeningClaim n Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest)
    (statement :
      let e := encodings binary prime P R cfg earlier output.request
      let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
      RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
        parent.point (parent.point.priorAnswers H) = some data)
    (opened :
      let e := encodings binary prime P R cfg earlier output.request
      let indices := cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2
      OrderedOpening.decode (cfg.bindSalt (e.context output.proof)) indices
        (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
          cfg.binaryRows cfg.primeRows cfg.openings output.proof) = some claim) :
    let e := encodings binary prime P R cfg earlier output.request
    let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
    let indices := cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2
    decode binary prime P R cfg earlier hashPublic decodePublic draw output H =
      some ⟨data.1,data.2,claim,RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2,
        OrderedOpening.query indices⟩ := by
  unfold decode
  simp only [statement,opened,Option.bind_eq_bind,Option.bind_some,Option.pure_def]

end LfzkV2.Current.RuntimeAdaptiveVerifier
