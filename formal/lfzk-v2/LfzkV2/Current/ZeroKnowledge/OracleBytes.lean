import LfzkV2.Current.CanonicalReplay
import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.ZeroKnowledge.OpeningFreshness

/-! Recovery from the actual physical opening preimage. An outside observer
may submit arbitrary byte strings, including malformed queries and repeated
queries. Equal bytes at the simulator's programmed input recover the same
root, the same four H/Z arrays and the same ancestor query inputs. Redundant
typed caches cannot create a second interpretation of a canonical preimage.

These are deterministic parser facts. They discharge the byte-to-value part
of a freshness argument; they do not assume or assert that an input is fresh. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleBytes

open CanonicalPrefix QueryRuntime
open scoped Classical
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (fits : g.roles.length < 2^64)

local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount

/-- The whole-input parser rejects an ignored suffix or malformed field cell.
It reconstructs caches from physical bytes rather than trusting a caller. -/
def decode (raw : Bytes) : Option Point :=
  ((QueryRuntime.Runtime.codec repr shape setup publicCount fits).decode raw).map Subtype.val

theorem decode_bytes (point : Point)
    (canonical : QueryRuntime.Runtime.Canonical repr shape setup publicCount point) :
    decode repr shape setup publicCount fits
      (QueryRuntime.Runtime.pointBytes repr shape setup publicCount fits point) = some point := by
  have h := (QueryRuntime.Runtime.codec repr shape setup publicCount fits).decode_encode
    ⟨point,canonical⟩
  exact congrArg (Option.map Subtype.val) h

theorem canonical_bytes_injective (first second : Point)
    (hfirst : QueryRuntime.Runtime.Canonical repr shape setup publicCount first)
    (hsecond : QueryRuntime.Runtime.Canonical repr shape setup publicCount second)
    (same : QueryRuntime.Runtime.pointBytes repr shape setup publicCount fits first =
      QueryRuntime.Runtime.pointBytes repr shape setup publicCount fits second) : first = second := by
  have h := congrArg (decode repr shape setup publicCount fits) same
  rw [decode_bytes repr shape setup publicCount fits first hfirst,
    decode_bytes repr shape setup publicCount fits second hsecond] at h
  exact Option.some.inj h

def root (raw : Bytes) : Option Digest :=
  (decode repr shape setup publicCount fits raw).map fun point => point.context.root

def responses (raw : Bytes) : Option (WireOpening.Responses g fields) := do
  let point ← decode repr shape setup publicCount fits raw
  point.readAt g.openingIndex.val (fun block => block.2.responses)

def primary (side : Side) (raw : Bytes) :
    Option (Fin (g.rowDimension+g.maskingDegree) → fields side) :=
  (responses repr shape setup publicCount fits raw).map fun response =>
    match side with
    | .binary => response.1.h
    | .prime => response.2.h

/-- Keeping the full decoded prefix together with H pins the earlier
batching query even when the commitment root depends on the primary mask. -/
def taggedPrimary (side : Side) (raw : Bytes) :
    Option (Point × (Fin (g.rowDimension+g.maskingDegree) → fields side)) := do
  let point ← decode repr shape setup publicCount fits raw
  let sample ← primary repr shape setup publicCount fits side raw
  pure (point,sample)

/-- Recover a strict ancestor from a physical preimage without asking an
oracle. Querying that ancestor later uses its actual complete preimage. -/
def ancestor (rank : ℕ) (raw : Bytes) : Option Point := do
  let point ← decode repr shape setup publicCount fits raw
  point.atRank rank

variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)



variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ maxLength)
variable (request : CanonicalRequest.Request shape publicCount)
variable (initial : Digest)
variable (proof : CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
variable (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)

include bodyFits

/-- Canonicality is proved from the current packet constructors. It is not
an acceptance, privacy or whole-replay correspondence assumption. -/
theorem replay_canonical (index : ℕ) (inside : index ≤ g.roles.length) :
    QueryRuntime.Runtime.Canonical repr shape setup publicCount
      (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H index) := by
  apply CanonicalReplay.Runtime.canonical_of_blocks repr shape setup publicCount
    (CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request)
    (fun proof index past => CanonicalRequest.ordinaryData shape publicCount
      binaryRequest metadata request proof.body index past)
    (fun proof index past zero => ?_)
    (fun proof index past positive => ?_)
    bodyFits initial proof H index inside
  · exact CanonicalRequest.block_zero repr shape setup publicCount binaryRequest metadata request
      proof index zero past
  · exact CanonicalRequest.block_pos repr shape setup publicCount binaryRequest metadata request
      proof index (by omega) past

def openingBytes : Bytes :=
  QueryRuntime.Runtime.pointBytes repr shape setup publicCount fits
    (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H g.openingIndex.val)


theorem decode_opening :
    decode repr shape setup publicCount fits
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H g.openingIndex.val) := by
  apply decode_bytes
  exact replay_canonical repr shape setup publicCount binaryRequest metadata bodyFits request
    initial proof H _ (Nat.le_of_lt g.openingIndex.isLt)

theorem opening_root :
    root repr shape setup publicCount fits
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some proof.body.commitment := by
  unfold root
  rw [decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  simp only [Option.map_some]
  rw [(CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).point_context]
  rfl

theorem opening_responses :
    responses repr shape setup publicCount fits
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some (proof.body.binaryBackend.response,proof.body.primeBackend.response) := by
  unfold responses
  rw [decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  change Input.readAt
    (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H g.openingIndex.val)
    g.openingIndex.val (fun block => block.2.responses) = _
  rw [(CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).readAt_replay initial proof H g.openingIndex.val
    (Nat.le_of_lt g.openingIndex.isLt) g.openingIndex (le_refl _) (fun block => block.2.responses)]
  rw [CanonicalRequest.block_opening]
  rfl

theorem opening_primary_binary :
    primary repr shape setup publicCount fits .binary
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some proof.body.binaryBackend.response.h := by
  unfold primary
  rw [opening_responses repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  rfl

theorem opening_primary_prime :
    primary repr shape setup publicCount fits .prime
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some proof.body.primeBackend.response.h := by
  unfold primary
  rw [opening_responses repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  rfl

theorem opening_tagged_binary :
    taggedPrimary repr shape setup publicCount fits .binary
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some
        ((((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
          proof H g.openingIndex.val),proof.body.binaryBackend.response.h) := by
  unfold taggedPrimary
  rw [decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H,
    opening_primary_binary repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  rfl

theorem opening_tagged_prime :
    taggedPrimary repr shape setup publicCount fits .prime
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some
        ((((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
          proof H g.openingIndex.val),proof.body.primeBackend.response.h) := by
  unfold taggedPrimary
  rw [decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H,
    opening_primary_prime repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  rfl

theorem opening_ancestor (index : ℕ) (earlier : index ≤ g.openingIndex.val) :
    ancestor repr shape setup publicCount fits index
        (openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H) =
      some (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point proof H index) := by
  unfold ancestor
  rw [decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H]
  exact (CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).point_atRank initial proof H g.openingIndex.val index
    (Nat.le_of_lt g.openingIndex.isLt) earlier

/-- A malformed observer query cannot equal the programmed opening input. -/
theorem malformed_ne_opening (raw : Bytes)
    (malformed : decode repr shape setup publicCount fits raw = none) :
    raw ≠ openingBytes repr shape setup publicCount fits binaryRequest metadata request initial proof H := by
  intro same
  rw [same,decode_opening repr shape setup publicCount fits binaryRequest metadata bodyFits request initial proof H] at malformed
  cases malformed

end LfzkV2.Current.ZeroKnowledge.OracleBytes

namespace LfzkV2.Current.ZeroKnowledge.OracleBytes

open Finset
open scoped Classical

/-- The counted event can be the actual raw-byte hit, rather than merely
membership in a set of typed oracle queries.  All prior queries, including
malformed strings and alternate encodings, are covered by the partial decoder.
The response identity is the backend's additive primary-mask formula. -/
theorem raw_hit_card {Mask Prefix : Type} [AddGroup Mask] [Fintype Mask]
    (historyOf : Mask → Prefix) (base : Prefix → Mask)
    (input : Mask → Bytes) (read : Bytes → Option (Prefix × Mask))
    (primaryFormula : ∀ mask,
      read (input mask) = some (OpeningFreshness.taggedResponse historyOf base mask))
    (prior : Finset Bytes) :
    (univ.filter fun mask => input mask ∈ prior).card ≤ prior.card := by
  apply le_trans _ (OpeningFreshness.prior_hit_card historyOf base read prior)
  apply card_le_card
  intro mask included
  rw [mem_filter] at included ⊢
  refine ⟨included.1,?_⟩
  exact mem_image.mpr ⟨input mask,included.2,primaryFormula mask⟩

theorem raw_hit_probability {Mask Prefix : Type} [AddGroup Mask] [Fintype Mask]
    (historyOf : Mask → Prefix) (base : Prefix → Mask)
    (input : Mask → Bytes) (read : Bytes → Option (Prefix × Mask))
    (primaryFormula : ∀ mask,
      read (input mask) = some (OpeningFreshness.taggedResponse historyOf base mask))
    (prior : Finset Bytes) :
    ((univ.filter fun mask => input mask ∈ prior).card : ℚ) / Fintype.card Mask ≤
      (prior.card : ℚ) / Fintype.card Mask :=
  div_le_div_of_nonneg_right
    (Nat.cast_le.mpr (raw_hit_card historyOf base input read primaryFormula prior))
    (Nat.cast_nonneg _)

end LfzkV2.Current.ZeroKnowledge.OracleBytes
