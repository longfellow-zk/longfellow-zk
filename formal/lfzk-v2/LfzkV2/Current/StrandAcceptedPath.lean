import LfzkV2.Current.StrandVerifier
import LfzkV2.Current.StrandReplay
import LfzkV2.Current.CanonicalVerifierAgreement

/-! The canonical runtime supplies the path used in strand query charging.
The submitted request and proof determine every reached packet through the
existing verifier. Query recovery is proved separately from this encoding bridge. Neither the path nor its history is an additional input. -/
noncomputable section
namespace LfzkV2.Current.StrandAcceptedPath
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Merkle.RandomOracle TranscriptV2
open scoped Classical
local instance : DecidableEq Strand.OtherPoint := Classical.decEq _

variable {g : Geometry} {fields : Fields} {Advice C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (fits : g.roles.length < 2^64)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)

local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "schema" => StrandRuntime.Runtime.schema repr shape setup binary.nPublic
local notation "history" => StrandRuntime.history bodyCodec
local notation "oracle" => TranscriptV2.StrandVerifier.oracle history sample cfg.fallback
local notation "beforeSeal" => TranscriptV2.StrandVerifier.beforeSeal history sample cfg.fallback (M)

/-- Parsed values are recovered from the actual reached verifier inputs.
Indices beyond the end are irrelevant to the path predicate and use the
final point, keeping this mathematical function total. -/
def value (output : Output) (SHA : Strand.Oracle) (index : ℕ) : Value :=
  (StrandRuntime.Runtime.valuesEquiv repr shape setup binary.nPublic fits).symm
    ⟨(M).point output (oracle SHA) (min index g.roles.length),
      CanonicalVerifierAgreement.point_canonical binary prime P R repr shape setup cfg binaryCount metadata bodyFits
        output (oracle SHA) _ (Nat.min_le_right _ _)⟩

theorem value_point (output : Output) (SHA : Strand.Oracle) (index : ℕ) (within : index ≤ g.roles.length) :
    QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic
      (value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA index) =
        (M).point output (oracle SHA) index := by
  unfold value
  rw [StrandRuntime.Runtime.valuesEquiv_symm]
  exact congrArg (fun i => (M).point output (oracle SHA) i) (Nat.min_eq_left within)

theorem value_history (output : Output) (SHA : Strand.Oracle) (index : ℕ) (within : index ≤ g.roles.length) :
    (schema).encode
      (value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA index) =
        history ((M).point output (oracle SHA) index) := by
  rw [← StrandRuntime.Runtime.toPoint_history,
    value_point binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA index within]

end LfzkV2.Current.StrandAcceptedPath
