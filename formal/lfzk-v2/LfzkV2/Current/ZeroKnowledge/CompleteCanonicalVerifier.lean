import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalCompletion
import LfzkV2.Current.ZeroKnowledge.CompleteProgrammedVerifier
import LfzkV2.Current.ZeroKnowledge.OracleRuntime
import LfzkV2.Current.ZeroKnowledge.CompleteTerminal
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalPublic
import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.MerkleWireCodec

/-! The complete simulator uses the current canonical request packets,
the indexed tuple Merkle bytes, one whole opening-answer replacement, and
the ordinary final seal. Its constructor receives public frontend data and
private random tapes, never a witness. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)

local notation "Cfg" => publicConfig binary prime binaryNodes primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R Cfg
local notation "Second" => RuntimeVerifier.second binary prime P R Cfg
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic

theorem encoded (request : CanonicalRequest.Request shape binary.nPublic) :
    RuntimeAdaptiveVerifier.encodings binary prime P R Cfg
      (earlier binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata) request =
      (encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request).encoding :=
  CanonicalRuntime.encodings_eq binary prime P R repr shape setup
    (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount metadata request

variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (publicConfig binary prime binaryNodes primeNodes repr shape setup cfg))

theorem filled_batchingPoint (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) (H : Point → Digest × C) :
    batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
      (body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend) H =
      batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
        (committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend) H := by
  simp only [batchingPoint,BackendPath.parent_point]
  change ((CanonicalRequest.encoding repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup
      (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount) metadata request).chain
    cfg.initialLink).point
      (CompleteTerminal.proof
        ⟨committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend,fun _ => 0⟩
        (body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend))
      H g.batchingIndex.val = _
  exact CompleteTerminal.point_before repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup
      (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount) metadata request cfg.initialLink
    _ _ H g.batchingIndex.val (by rw [g.openingIndex_val]; omega)

theorem accepts (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) (H : Point → Digest × C) (answer : Digest × C)
    (chosen : cfg.sample answer.2 = indices)
    (parsed :
      let full := body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend
      let e := encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
      let parent := BackendPath.parent e.encoding cfg.initialLink ⟨full,fun _ => 0⟩ H g.batchingIndex
      RuntimeAdaptive.statementAt binary prime P R Cfg (CanonicalRequest.hashPublic binary.nPublic)
        (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
          (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount)
        parent.point (parent.point.priorAnswers H) = some data)
    (coinMatches :
      let full := body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend
      let e := encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
      let parent := BackendPath.parent e.encoding cfg.initialLink ⟨full,fun _ => 0⟩ H g.batchingIndex
      RuntimeVerifier.batchingDecoder binary prime P R Cfg draw (H parent.point).2 = coin) :
    let result := simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata
      request HM indices nonces tape data coin frontend H answer
    RuntimeAdaptiveVerifier.verify binary prime P R Cfg
      (earlier binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
        (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount)
      draw (merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg) HM result.1 result.2 = true := by
  letI := leafInhabited binary prime binaryNodes primeNodes repr shape setup cfg
  exact CompleteProgrammedVerifier.accepts binary prime binaryNodes primeNodes Cfg
    (earlier binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata)
    (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
      (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount)
    draw (merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg)
    request (encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request)
    (encoded binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request)
    HM indices nonces tape data coin frontend setup.jointContext H answer chosen parsed coinMatches rfl rfl rfl

/-- Every successful result of the total public completion algorithm is
accepted. Parser failure is represented explicitly by `none`, rather than
hidden in a supplied application or backend correctness certificate. -/
theorem complete_success_accepts (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (frontend : Body) (H : Point → Digest × C) (answer : Digest × C)
    (result : CanonicalRuntime.Output (Advice := Advice) binary shape × (Point → Digest × C))
    (chosen : cfg.sample answer.2 = indices)
    (completed : complete binary prime binaryNodes primeNodes repr shape setup cfg
      binaryCount primeCount metadata draw request HM indices nonces tape frontend H answer = some result) :
    RuntimeAdaptiveVerifier.verify binary prime P R Cfg
      (earlier binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
        (basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount)
      draw (merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg) HM result.1 result.2 = true := by
  let early := committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend
  cases parsed : statementAt binary prime binaryNodes primeNodes repr shape setup cfg
      binaryCount primeCount metadata request early H with
  | none =>
      dsimp only [early] at parsed
      dsimp only [complete] at completed
      rw [parsed] at completed
      cases completed
  | some data =>
      dsimp only [early] at parsed
      dsimp only [complete] at completed
      rw [parsed] at completed
      have same := Option.some.inj completed
      subst result
      apply accepts binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata draw
        request HM indices nonces tape data _ frontend H answer chosen
      · change statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata
          request (body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data _ frontend) H = some data
        unfold statementAt
        rw [filled_batchingPoint]
        exact parsed
      · change RuntimeVerifier.batchingDecoder binary prime P R Cfg draw
          (H (batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
            (body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data _ frontend) H)).2 = _
        rw [filled_batchingPoint]
        rfl

end LfzkV2.Current.ZeroKnowledge.CompleteCanonicalVerifier
