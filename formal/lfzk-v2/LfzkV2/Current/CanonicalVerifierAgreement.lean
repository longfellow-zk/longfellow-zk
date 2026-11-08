import LfzkV2.Current.CanonicalReplay
import LfzkV2.Current.CanonicalRuntime

/-! The actual canonical runtime verifier ignores malformed logical cache
aliases. Agreement on canonical physical prefixes preserves its full replay,
late decoding and final-seal check, including adaptively chosen requests. -/
noncomputable section
namespace LfzkV2.Current.CanonicalVerifierAgreement
open Application ApplicationSetup QueryRuntime
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
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
include bodyFits

local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output binary shape
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R (W)
local notation "Canonical" => QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic

/-- Actual body/request packets construct the entire canonical replay.
The last point binds the actual canonical complete proof body. -/
theorem point_canonical (output : Output) (H : Point → Digest × C)
    (index : ℕ) (hi : index ≤ g.roles.length) : Canonical ((M).point output H index) := by
  rw [RuntimeAdaptiveVerifier.point_eq,CanonicalRuntime.encodings_eq]
  apply CanonicalReplay.Runtime.canonical_of_blocks repr shape setup binary.nPublic (Earlier output.request)
    (fun proof i past => CanonicalRequest.ordinaryData shape binary.nPublic
      (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
      metadata output.request proof.body i past)
    ?_ ?_ bodyFits cfg.initialLink output.proof H index hi
  · intro proof i past hz
    exact CanonicalRequest.block_zero repr shape setup binary.nPublic
      (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
      metadata output.request proof i hz past
  · intro proof i past hp
    exact CanonicalRequest.block_pos repr shape setup binary.nPublic
      (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
      metadata output.request proof i (by omega) past

/-- Whole-state equality retains both the physical prefix and every actual
challenge answer used to construct later statements. -/
theorem replay_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point)
    (index : ℕ) (hi : index ≤ g.roles.length) :
    (M).replay output H index = (M).replay output H' index := by
  apply (M).replay_congr_prefix
  intro j hj
  exact agree _ (point_canonical binary prime P R repr shape setup cfg binaryCount metadata bodyFits
    output H j (by omega))

theorem point_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point)
    (index : ℕ) (hi : index ≤ g.roles.length) :
    (M).point output H index = (M).point output H' index :=
  congrArg (M).input (replay_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
    output H H' agree index hi)

/-- This includes the final seal answer, not just ordinary round answers. -/
theorem point_answer_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point)
    (index : ℕ) (hi : index ≤ g.roles.length) :
    H ((M).point output H index) = H' ((M).point output H' index) :=
  (agree _ (point_canonical binary prime P R repr shape setup cfg binaryCount metadata bodyFits output H index hi)).trans
    (congrArg H' (point_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits output H H' agree index hi))

private theorem member_point_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point)
    (index : ℕ) (hi : index ≤ g.roles.length) :
    (((RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).chain cfg.initialLink).point
      output.proof H index) =
    (((RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).chain cfg.initialLink).point
      output.proof H' index) := by
  exact (RuntimeAdaptiveVerifier.point_eq binary prime P R (W) (Earlier) output H index).symm.trans
    ((point_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits output H H' agree index hi).trans
      (RuntimeAdaptiveVerifier.point_eq binary prime P R (W) (Earlier) output H' index))

private theorem member_answer_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point)
    (index : ℕ) (hi : index ≤ g.roles.length) :
    H (((RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).chain cfg.initialLink).point
      output.proof H index) =
    H' (((RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).chain cfg.initialLink).point
      output.proof H' index) := by
  exact (congrArg H (RuntimeAdaptiveVerifier.point_eq binary prime P R (W) (Earlier) output H index)).symm.trans
    ((point_answer_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits output H H' agree index hi).trans
      (congrArg H' (RuntimeAdaptiveVerifier.point_eq binary prime P R (W) (Earlier) output H' index)))

variable (primeCount : shape.primePublic = prime.nPublic)
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg))
variable [Inhabited (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf]

/-- The backend parent, its strict earlier answers, the batching coin and
the shared opening set are all invariant. No late statement is supplied. -/
theorem decode_eq (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point) :
    RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      draw output H =
    RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      draw output H' := by
  let e := RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request
  let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
  let parent' := BackendPath.parent e cfg.initialLink output.proof H' g.batchingIndex
  have hp : parent = parent' := by
    apply BackendQueries.Parent.point_injective (Body := Body g fields Advice (OpeningBody.Authentication g))
    rw [BackendPath.parent_point,BackendPath.parent_point]
    exact member_point_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
      output H H' agree g.batchingIndex.val g.batchingIndex.isLt.le
  have ha : H parent.point = H' parent'.point := by
    rw [BackendPath.parent_point,BackendPath.parent_point]
    exact member_answer_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
      output H H' agree g.batchingIndex.val g.batchingIndex.isLt.le
  have hprior : parent.point.priorAnswers H = parent'.point.priorAnswers H' := by
    rw [BackendPath.priorAnswers_replay,BackendPath.priorAnswers_replay]
    funext j
    exact congrArg Prod.snd (member_answer_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
      output H H' agree j.val (by have := j.isLt; have := g.batchingIndex.isLt; omega))
  have hs : RuntimeAdaptive.statementAt binary prime P R (W) (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      parent.point (parent.point.priorAnswers H) =
    RuntimeAdaptive.statementAt binary prime P R (W) (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount)
      parent'.point (parent'.point.priorAnswers H') := by
    rw [hprior,hp]
  have hquery := member_answer_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
    output H H' agree g.openingIndex.val g.openingIndex.isLt.le
  unfold RuntimeAdaptiveVerifier.decode
  change Option.bind _ (fun data => Option.bind _ (fun claim => some _)) =
    Option.bind _ (fun data => Option.bind _ (fun claim => some _))
  erw [hs,hquery,ha]
  rfl

variable (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf Digest Enc)

omit [Inhabited (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf] in
/-- Merkle verification itself is unchanged. Its final seal reads the same
canonical last query answer under the two oracles. -/
theorem checks_iff (HM : Enc → Digest) (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ point, Canonical point → H point = H' point) (decoded : Decoded) :
    RuntimeAdaptiveVerifier.Checks binary prime P R (W) (Earlier) codec HM output H decoded ↔
      RuntimeAdaptiveVerifier.Checks binary prime P R (W) (Earlier) codec HM output H' decoded := by
  have ha := point_answer_eq binary prime P R repr shape setup cfg binaryCount metadata bodyFits
    output H H' agree g.roles.length (Nat.le_refl _)
  change H ((M).finalSealPoint output H) = H' ((M).finalSealPoint output H') at ha
  unfold RuntimeAdaptiveVerifier.Checks
  rw [ha]

end LfzkV2.Current.CanonicalVerifierAgreement
