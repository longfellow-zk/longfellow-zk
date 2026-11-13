import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.RequestedApplication
import LfzkV2.Current.RuntimeAdaptiveStatement

/-! The runtime verifier with canonical request packets. Public values are
read back from their actual boundaries, and the mandatory backend opening
encoder reproduces those same bytes. Field representations and trusted
circuit topology are public setup, not per-proof correspondence records. -/
noncomputable section
namespace LfzkV2.Current.CanonicalRuntime
open Application ApplicationSetup RuntimeAdaptive QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "WireBase" => CanonicalRequest.Base repr shape setup binary.nPublic
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)

abbrev Request := CanonicalRequest.Request shape binary.nPublic
abbrev Point := QueryRuntime.Runtime.Point repr shape setup binary.nPublic

/-- These callbacks are determined by the actual wire format. The other
fields retain the checked arithmetic and ideal challenge-reader setup. -/
def wirePublic : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt) :=
  { cfg with
    openingBase := WireOpening.openingBase shape repr setup binary.nPublic
    root := FingerprintPrefix.Key.root
    authenticationContext := fun _ => setup.jointContext }

def binaryRequest (bits : Fin binary.nPublic → Bool) (i : Fin shape.binaryPublic) : fields .binary :=
  cfg.binaryField.symm (Adapter.Circuit.bitValue (bits (Fin.cast binaryCount i)))

def primeInputs (request : Request binary shape) : Fin prime.nPublic → N :=
  fun i => cfg.primeField (request.primeInputs (Fin.cast primeCount.symm i))

def decodePrimePublic (base : WireBase) : Option (Fin prime.nPublic → N) :=
  (CanonicalRequest.decodePrimePublic repr shape setup binary.nPublic base).map
    (fun values i => cfg.primeField (values (Fin.cast primeCount.symm i)))

variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)

def earlier (request : Request binary shape) :=
  CanonicalRequest.encoding repr shape setup binary.nPublic
    (binaryRequest binary prime P R repr shape setup cfg binaryCount) metadata request

/-- The complete runtime's two mandatory filling passes change no bytes
or caches of the canonical request encoder. -/
theorem encodings_eq (request : Request binary shape) :
    RuntimeAdaptiveVerifier.encodings binary prime P R (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata) request =
      earlier binary prime P R repr shape setup cfg binaryCount metadata request := by
  exact CanonicalRequest.withBackendOpening_eq repr shape setup binary.nPublic
    (binaryRequest binary prime P R repr shape setup cfg binaryCount) metadata
    (RuntimeVerifier.first binary prime P R cfg) (RuntimeVerifier.second binary prime P R cfg)
    cfg.binaryField cfg.primeField cfg.rowDimension cfg.maskingDegree
    (RuntimeVerifier.productFits binary prime P R cfg) request

omit [DecidableEq B] in
theorem hashPublic_replay (request : Request binary shape) (initial : Digest)
    (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point binary repr shape setup → Digest × C) (index : ℕ) :
    CanonicalRequest.hashPublic binary.nPublic
      (((earlier binary prime P R repr shape setup cfg binaryCount metadata request).chain initial).point
        proof H index).context = some request.publicBits :=
  CanonicalRequest.hashPublic_replay repr shape setup binary.nPublic
    (binaryRequest binary prime P R repr shape setup cfg binaryCount) metadata request initial proof H index

omit [DecidableEq B] in
/-- The scalar parser and field representation recover exactly the late
request vector. The count casts change only indices, not values or bytes. -/
theorem primePublic_replay (request : Request binary shape) (initial : Digest)
    (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
    (H : Point binary repr shape setup → Digest × C) (index : ℕ)
    (hi : index ≤ g.roles.length) (hstart : g.primeStart ≤ index) :
    RuntimeAdaptive.primePublic prime (decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      (((earlier binary prime P R repr shape setup cfg binaryCount metadata request).chain initial).point
        proof H index) = some (primeInputs binary prime P R repr shape setup cfg primeCount request) := by
  change (((earlier binary prime P R repr shape setup cfg binaryCount metadata request).chain initial).point
    proof H index).readAt (CanonicalRequest.primeBoundary g).val
      (fun block => decodePrimePublic binary prime P R repr shape setup cfg primeCount block.1) = _
  rw [Replay.Encoding.readAt_replay _ _ _ _ _ hi (CanonicalRequest.primeBoundary g) hstart]
  change (CanonicalRequest.decodePrimePublic repr shape setup binary.nPublic
    ((CanonicalRequest.encoding repr shape setup binary.nPublic
      (binaryRequest binary prime P R repr shape setup cfg binaryCount) metadata request).block
        proof (CanonicalRequest.primeBoundary g) _).1).map
          (fun values i => cfg.primeField (values (Fin.cast primeCount.symm i))) = _
  have h := CanonicalRequest.readPrimePublic_block repr shape setup binary.nPublic
    (binaryRequest binary prime P R repr shape setup cfg binaryCount) metadata request proof
    (CanonicalRequest.primeBoundary g) rfl
  unfold CanonicalRequest.decodePrimePublic
  rw [h]
  rfl

abbrev Output := RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice)
  (Request := Request binary shape)

def batchingPoint (output : Output binary shape) (H : Point binary repr shape setup → Digest × C) :=
  (RuntimeAdaptiveVerifier.chain binary prime P R (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)).point output H g.batchingIndex.val

/-- At the backend boundary both parsed public vectors are precisely the
chosen request. The early key still omits the late prime vector. -/
theorem batching_publics (output : Output binary shape)
    (H : Point binary repr shape setup → Digest × C) :
    CanonicalRequest.hashPublic binary.nPublic
      (batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H).context =
      some output.request.publicBits ∧
    RuntimeAdaptive.primePublic prime (decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      (batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H) =
      some (primeInputs binary prime P R repr shape setup cfg primeCount output.request) := by
  unfold batchingPoint
  rw [RuntimeAdaptiveVerifier.point_eq,encodings_eq]
  exact ⟨hashPublic_replay binary prime P R repr shape setup cfg binaryCount metadata output.request
    cfg.initialLink output.proof H g.batchingIndex.val,
    primePublic_replay binary prime P R repr shape setup cfg binaryCount primeCount metadata output.request
      cfg.initialLink output.proof H g.batchingIndex.val g.batchingIndex.isLt.le (by
        simp only [Geometry.batchingIndex_val,Geometry.backendPrefix,Geometry.primeStart,
          List.length_append,List.length_cons,List.length_nil]
        omega)⟩

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (wirePublic binary prime P R repr shape setup cfg))
variable [Inhabited (RuntimeVerifier.Family binary prime P R
  (wirePublic binary prime P R repr shape setup cfg)).Leaf]

/-- Successful runtime decoding builds the application for the actual
request; an adversarially supplied decoded system is not part of this API. -/
theorem decoded_request (output : Output binary shape)
    (H : Point binary repr shape setup → Digest × C)
    (decoded : RuntimeVerifier.Decoded binary prime P R (wirePublic binary prime P R repr shape setup cfg))
    (hdecode : RuntimeAdaptiveVerifier.decode binary prime P R
      (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw output H = some decoded) :
    let point := batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H
    ApplicationPrefix.decodeChecked (binaryWithBits binary output.request.publicBits)
      (primeWithInputs prime (primeInputs binary prime P R repr shape setup cfg primeCount output.request))
      cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
      cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice
      cfg.fallback point (point.priorAnswers H) = some decoded.application := by
  have hs := (RuntimeAdaptiveVerifier.decode_spec binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)
    (CanonicalRequest.hashPublic binary.nPublic)
    (decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw output H decoded hdecode).1
  rw [BackendPath.parent_point] at hs
  have ha := (RuntimeAdaptiveStatement.statementAt_spec binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (CanonicalRequest.hashPublic binary.nPublic)
    (decodePrimePublic binary prime P R repr shape setup cfg primeCount) _ _ _ hs).1
  have hp := batching_publics binary prime P R repr shape setup cfg binaryCount primeCount metadata output H
  have he : (((RuntimeAdaptiveVerifier.encodings binary prime P R
      (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata) output.request).chain
        (wirePublic binary prime P R repr shape setup cfg).initialLink).point
      output.proof H g.batchingIndex.val) =
      batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H := by
    exact (RuntimeAdaptiveVerifier.point_eq binary prime P R
      (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata) output H g.batchingIndex.val).symm
  rw [he] at ha
  rw [RequestedApplication.application_eq binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (CanonicalRequest.hashPublic binary.nPublic)
    (decodePrimePublic binary prime P R repr shape setup cfg primeCount) _ _
    output.request.publicBits (primeInputs binary prime P R repr shape setup cfg primeCount output.request)
    hp.1 hp.2] at ha
  exact ha


/-- The same extracted pair satisfies the two circuits at the actual
request's public values. Both frontend payloads and the generated binary
circuit are reconstructed from successful decoding of this proof prefix;
none is supplied as an additional correctness certificate. -/
theorem decoded_true_at_request (output : Output binary shape)
    (H : Point binary repr shape setup → Digest × C)
    (decoded : RuntimeVerifier.Decoded binary prime P R (wirePublic binary prime P R repr shape setup cfg))
    (hdecode : RuntimeAdaptiveVerifier.decode binary prime P R
      (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (CanonicalRequest.hashPublic binary.nPublic)
      (decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw output H = some decoded)
    (w : Selection.Pair B N binary.Original prime.Original)
    (htrue : decoded.application.True w) :
    let point := batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H
    let requestedPrime := primeWithInputs prime
      (primeInputs binary prime P R repr shape setup cfg primeCount output.request)
    let requestedBinary := binaryWithBits binary output.request.publicBits
    ∃ (nd : PrimeData requestedPrime C)
      (bd : BinaryData requestedBinary nd (cfg.polynomialX^Adapter.Mdoc.generatorExponent)),
      ApplicationPrefix.readPrime requestedPrime cfg.primeField cfg.primeDecode cfg.primeNonzero
        cfg.fallback point (point.priorAnswers H) = some nd ∧
      ApplicationPrefix.readBinary requestedBinary nd (cfg.polynomialX^Adapter.Mdoc.generatorExponent)
        cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
        cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback point (point.priorAnswers H) = some bd ∧
      bd.setup.circuit.Satisfies (requestedBinary.inputs bd.entries
        (ApplicationViews.binaryValues requestedBinary requestedPrime w)) ∧
      prime.circuit.Satisfies (ApplicationViews.primeInputs requestedBinary requestedPrime w) := by
  let point := batchingPoint binary prime P R repr shape setup cfg binaryCount metadata output H
  let requestedPrime := primeWithInputs prime
    (primeInputs binary prime P R repr shape setup cfg primeCount output.request)
  let requestedBinary := binaryWithBits binary output.request.publicBits
  have hchecked := decoded_request binary prime P R repr shape setup cfg binaryCount primeCount
    metadata draw output H decoded hdecode
  obtain ⟨nd,bd,hprime,hbinary,happlication⟩ := ApplicationPrefix.decodeChecked_spec
    requestedBinary requestedPrime cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree
    cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero
    cfg.conversion cfg.advice cfg.fallback point (point.priorAnswers H) decoded.application hchecked
  exact ⟨nd,bd,hprime,hbinary,RequestedApplication.checked_true binary prime P R cfg
    output.request.publicBits (primeInputs binary prime P R repr shape setup cfg primeCount output.request)
    nd bd decoded.application happlication w htrue⟩

end LfzkV2.Current.CanonicalRuntime
