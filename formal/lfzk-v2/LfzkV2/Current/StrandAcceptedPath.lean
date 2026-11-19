import LfzkV2.Current.Format
import LfzkV2.Current.StrandVerifier

import LfzkV2.Current.CanonicalRuntime

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
variable (fmt : Format g fields Advice binary.nPublic)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := fmt.Base)
  (Key := fmt.Key) (C := C) (Salt := Salt))
variable (binaryCount : fmt.binaryPublic = binary.nPublic)
variable (metadata : fmt.RequestMetadata C)
variable (bodyFits : fmt.bodyBound ≤ CanonicalPrefix.maxLength)
variable (fits : g.roles.length < 2^64)
variable (sample : fmt.Point →
  Tree Strand.Word Digest (Option C) blocks)

local notation "W" => CanonicalRuntime.wirePublic binary prime P R fmt cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R fmt cfg binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "Value" => fmt.Value
local notation "Point" => fmt.Point
local notation "Output" => CanonicalRuntime.FormatOutput binary fmt
local notation "bodyCodec" => fmt.body
local notation "schema" => fmt.schema
local notation "history" => StrandRuntime.history fmt.wire bodyCodec
local notation "oracle" => TranscriptV2.StrandVerifier.oracle history sample cfg.fallback
local notation "beforeSeal" => TranscriptV2.StrandVerifier.beforeSeal history sample cfg.fallback (M)

include bodyFits in
/-- Actual body/request packets construct the entire canonical replay.
The last point binds the actual canonical complete proof body. -/
theorem point_canonical (output : Output) (H : Point → Digest × C)
    (index : ℕ) (hi : index ≤ g.roles.length) : fmt.Canonical ((M).point output H index) := by
  rw [RuntimeAdaptiveVerifier.point_eq,CanonicalRuntime.encodings_eq]
  exact fmt.point_canonical (CanonicalRuntime.binaryRequest binary prime P R fmt cfg binaryCount)
    metadata output.request bodyFits cfg.initialLink output.proof H index hi


/-- Parsed values are recovered from the actual reached verifier inputs.
Indices beyond the end are irrelevant to the path predicate and use the
final point, keeping this mathematical function total. -/
def value (output : Output) (SHA : Strand.Oracle) (index : ℕ) : Value :=
  (fmt.boundedValuesEquiv fits).symm
    ⟨(M).point output (oracle SHA) (min index g.roles.length),
      point_canonical binary prime P R fmt cfg binaryCount metadata bodyFits
        output (oracle SHA) _ (Nat.min_le_right _ _)⟩

theorem value_point (output : Output) (SHA : Strand.Oracle) (index : ℕ) (within : index ≤ g.roles.length) :
    fmt.toPoint
      (value binary prime P R fmt cfg binaryCount metadata bodyFits fits sample output SHA index) =
        (M).point output (oracle SHA) index := by
  unfold value
  rw [Format.boundedValuesEquiv,Format.valuesEquiv_symm]
  exact congrArg (fun i => (M).point output (oracle SHA) i) (Nat.min_eq_left within)

theorem value_history (output : Output) (SHA : Strand.Oracle) (index : ℕ) (within : index ≤ g.roles.length) :
    (schema).encode
      (value binary prime P R fmt cfg binaryCount metadata bodyFits fits sample output SHA index) =
        history ((M).point output (oracle SHA) index) := by
  rw [← Format.toPoint_history,
    value_point binary prime P R fmt cfg binaryCount metadata bodyFits fits sample output SHA index within]

end LfzkV2.Current.StrandAcceptedPath
