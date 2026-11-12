import LfzkV2.Current.StrandSealIndependence
import LfzkV2.Current.StrandWindow
import LfzkV2.Current.ConcreteMetadata
import TranscriptV2.CompositionTransport

/-! The actual complete-proof final seal, charged against the original
prover trace. Verifier replay is used to compute the address, but its queries
are never added to the prover's queried set. -/
noncomputable section
namespace LfzkV2.Current.StrandOriginalSeal
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Finset Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B Salt : Type}
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
variable (independent : CanonicalRequest.ChallengeIndependent shape binary.nPublic metadata)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)

local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "address" => StrandVerifier.finalSealAddress binary prime P R (W) (Earlier) bodyCodec sample
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape

variable (other : Finset Strand.OtherPoint) (fallback : StrandWindow.Node other)
local notation "Raw" => StrandWindow.Point other
local notation "encode" => StrandWindow.decode other fallback

def finiteAddress (output : Output) (G : Raw → Digest) : Raw :=
  encode (address output (G ∘ encode))

local notation "point" => finiteAddress binary prime P R repr shape setup cfg binaryCount metadata sample other fallback

private theorem address_prf (output : Output) (G : Strand.Oracle) :
    ∃ key : Strand.PrfKey, address output G = (Strand.Input.prf key.1 key.2 0).encode := ⟨(_, _),rfl⟩

include independent in
theorem finiteAddress_off (output : Output) (G G' : Raw → Digest)
    (agree : Bcs.TotalOracle.AgreeOff (point output G) G G') :
    point output G = point output G' := by
  have selected : ∃ digest, point output G = .inr (digest,0) := by
    obtain ⟨digest,same⟩ := address_prf binary prime P R repr shape setup cfg binaryCount metadata sample
      output (G ∘ encode)
    refine ⟨digest,?_⟩
    change encode (address output (G ∘ encode)) = _
    rw [same]
    exact StrandWindow.decode_encode other fallback (.inr (digest,0))
  obtain ⟨digest,selected⟩ := selected
  apply congrArg encode
  apply StrandSealIndependence.finalSealAddress_congr binary prime P R repr shape setup cfg binaryCount
    metadata independent sample output (G ∘ encode) (G' ∘ encode)
  intro history
  obtain ⟨node,same⟩ := StrandWindow.decode_history other fallback history
  apply agree
  rw [same,selected]
  exact Sum.inl_ne_inr

variable {fuel : ℕ} (program : Tree Bytes Digest (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)

/-- The finite address restriction preserves the original raw query set
exactly at every PRF address, including malformed or out-of-window inputs. -/
theorem unqueriedSeal_map (G : Raw → Digest) :
    StrandSealCharging.UnqueriedSeal point (fun output => output.proof.finalSeal)
        (mapQueries encode program) G ↔
      StrandSealCharging.UnqueriedSeal address (fun output => output.proof.finalSeal)
        program (G ∘ encode) := by
  let raw := address (program.run (G ∘ encode)).1 (G ∘ encode)
  obtain ⟨stream,shape⟩ := address_prf binary prime P R repr shape setup cfg binaryCount metadata sample
    (program.run (G ∘ encode)).1 (G ∘ encode)
  change raw = (Strand.Input.prf stream.1 stream.2 0).encode at shape
  have member : encode raw ∈ (seen program (G ∘ encode)).image encode ↔
      raw ∈ seen program (G ∘ encode) := by
    constructor
    · intro present
      obtain ⟨input,present,equal⟩ := Finset.mem_image.mp present
      have prf : encode raw = .inr (stream,0) := by
        rw [shape]
        exact StrandWindow.decode_encode other fallback (.inr (stream,0))
      have same := StrandWindow.decode_prf_fiber other fallback input stream 0 (equal.trans prf)
      have sameRaw : input = raw := same.trans shape.symm
      rw [sameRaw] at present
      exact present
    · exact Finset.mem_image_of_mem encode
  simp only [StrandSealCharging.UnqueriedSeal,run_mapQueries,finiteAddress,TranscriptV2.seen_mapQueries]
  exact and_congr (not_congr member) Iff.rfl

include independent in
/-- For an adaptive prover, a correct seal absent from its original raw
trace has probability at most one SHA-256 digest guess. The theorem permits
all node collisions, arbitrary sampler behavior, and adaptive public inputs.
It makes no assumption about the order in which the prover made queries. -/
theorem original_ratio_le :
    density (fun G : Raw → Digest =>
      StrandSealCharging.UnqueriedSeal address (fun output => output.proof.finalSeal)
        program (G ∘ encode)) ≤ 1 / (2^256 : ℚ) := by
  have law := density_congr (unqueriedSeal_map binary prime P R repr shape setup cfg binaryCount metadata
    sample other fallback program)
  rw [← law]
  have bound := StrandSealCharging.unqueriedSeal_density_le point (fun output => output.proof.finalSeal)
    (finiteAddress_off binary prime P R repr shape setup cfg binaryCount metadata independent sample other fallback)
    (mapQueries encode program)
  have size : (Fintype.card Digest : ℚ) = (2^256 : ℚ) := by
    rw [Strand.digest_card,Nat.cast_pow,Nat.cast_ofNat]
  exact bound.trans_eq (congrArg (fun value : ℚ => 1 / value) size)

variable {Enc : Type}
variable (hashPublic : FingerprintPrefix.Key binary.nPublic → Option (Fin binary.nPublic → Bool))
variable (decodePublic : CanonicalRequest.Base repr shape setup binary.nPublic →
  Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg))
variable [Inhabited (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)

include independent in
/-- The same bound applies directly to acceptance by the modeled runtime,
because the complete verifier checks precisely this seal. -/
theorem accepted_original_ratio_le :
    density (fun G : Raw → Digest =>
      let SHA := G ∘ encode
      let output := (program.run SHA).1
      StrandVerifier.verify binary prime P R (W) (Earlier) bodyCodec sample
          hashPublic decodePublic draw codec SHA merkleInput output = true ∧
        address output SHA ∉ seen program SHA) ≤ 1 / (2^256 : ℚ) := by
  apply le_trans _ (original_ratio_le binary prime P R repr shape setup cfg binaryCount metadata
    independent sample other fallback program)
  apply density_mono
  intro G accepted
  refine ⟨accepted.2,?_⟩
  obtain ⟨_,_,checks⟩ := (StrandVerifier.verify_true_iff binary prime P R (W) (Earlier) bodyCodec
    sample hashPublic decodePublic draw codec (G ∘ encode) merkleInput (program.run (G ∘ encode)).1).mp
      accepted.1
  exact checks.2.2.2.2.1

variable (params : ConcreteMetadata.Public binary prime shape)
local notation "concrete" => ConcreteMetadata.metadata (Advice := Advice) (C := C) binary prime shape params setup
local notation "concreteEarlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg params.binaryCount concrete

/-- The concrete metadata constructor discharges challenge independence.
The caller supplies no oracle-independence or replay-collision certificate. -/
theorem concrete_original_ratio_le :
    density (fun G : Raw → Digest =>
      let SHA := G ∘ encode
      let output := (program.run SHA).1
      StrandVerifier.verify binary prime P R (W) (concreteEarlier) bodyCodec sample
          hashPublic decodePublic draw codec SHA merkleInput output = true ∧
        StrandVerifier.finalSealAddress binary prime P R (W) (concreteEarlier) bodyCodec sample output SHA ∉
          seen program SHA) ≤ 1 / (2^256 : ℚ) := by
  exact accepted_original_ratio_le binary prime P R repr shape setup cfg params.binaryCount concrete
    (ConcreteMetadata.metadata_challengeIndependent binary prime shape params setup)
    sample other fallback program hashPublic decodePublic draw codec merkleInput

end LfzkV2.Current.StrandOriginalSeal
