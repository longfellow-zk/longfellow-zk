import LfzkV2.Current.RuntimeAdaptiveVerifier
import LfzkV2.Current.StrandRuntime
import Bcs.Indexed
import LfzkV2.Current.BackendPrefix

/-! The adaptive runtime verifier with SHA-strand finalization. Application
decoding, affine statements and tuple authentication reuse the existing
runtime checks. Only the transcript oracle and complete-proof seal differ.
Sampler failure is rejecting, so mathematical failure padding never supplies
an accepted runtime challenge. The complete soundness composition additionally
needs the concrete role samplers and the shared first-fingerprint extractor. -/
noncomputable section
namespace LfzkV2.Current.StrandVerifier
open Application ApplicationSetup CanonicalPrefix
open Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t capacity blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := BoundedBytes capacity)) C)
variable (bodyCodec : PrefixCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
variable (sample : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) →
    Tree TranscriptV2.Strand.Word Digest (Option C) blocks)

local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "history" => StrandRuntime.history bodyCodec

/-- Replaying the physical sampler determines the original typed runtime
answers. Unused failure values are harmless because `samplersSucceeded`
is checked on every ordinary boundary before accepting. -/
def oracle (G : TranscriptV2.Strand.Oracle) : Point → Digest × C :=
  TranscriptV2.StrandVerifier.oracle history sample cfg.fallback G

def samplersSucceeded (output : Output) (G : TranscriptV2.Strand.Oracle) : Prop :=
  ∀ i : Fin g.roles.length, TranscriptV2.StrandVerifier.sampled history sample G
    ((M).point output (oracle binary prime P R cfg bodyCodec sample G) i.val)

/-- The stored final seal is a challenge of the final node, not that node's
hash. The node is reconstructed from the actual submitted complete body. -/
def finalSealAddress (output : Output) (G : TranscriptV2.Strand.Oracle) : Bytes :=
  (TranscriptV2.Strand.Input.prf
    (history ((M).finalSealPoint output (oracle binary prime P R cfg bodyCodec sample G))).id
    (G (history ((M).finalSealPoint output (oracle binary prime P R cfg bodyCodec sample G))).input.encode) 0).encode

def finalSeal (output : Output) (G : TranscriptV2.Strand.Oracle) : Digest :=
  G (finalSealAddress binary prime P R cfg earlier bodyCodec sample output G)

theorem finalSeal_body (output : Output) (G : TranscriptV2.Strand.Oracle) :
    ∃ state, finalSeal binary prime P R cfg earlier bodyCodec sample output G =
      G (TranscriptV2.Strand.Input.prf
        state.id
        (G (TranscriptV2.StrandTranscript.finalNodeInput state (bodyCodec.encode output.proof.body))) 0).encode := by
  let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
  obtain ⟨state,encoded⟩ := StrandRuntime.complete_body_node bodyCodec e cfg.initialLink output.proof
    (oracle binary prime P R cfg bodyCodec sample G)
  have ids := TranscriptV2.StrandTranscript.finalNodeInput_id _ state _
    (TranscriptV2.Strand.History.valid _) encoded
  rw [TranscriptV2.Strand.History.input_id] at ids
  refine ⟨state,?_⟩
  unfold finalSeal finalSealAddress
  rw [RuntimeAdaptiveVerifier.finalSealPoint_eq]
  rw [encoded,ids]

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : BoundedBytes capacity → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)

def prefixZeros (output : Output) : Prop :=
  BackendPrefix.Zero (RuntimeVerifier.first binary prime P R cfg).participant
    (RuntimeVerifier.responses binary prime P R cfg output.proof).1 ∧
  BackendPrefix.Zero (RuntimeVerifier.second binary prime P R cfg).participant
    (RuntimeVerifier.responses binary prime P R cfg output.proof).2

def Checks (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output)
    (decoded : Decoded) : Prop :=
  let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
  let key := e.context output.proof
  samplersSucceeded binary prime P R cfg earlier bodyCodec sample output SHA ∧
  cfg.root key = output.proof.body.commitment ∧
  output.proof.body.authentication.context = cfg.authenticationContext key ∧
  ((RuntimeVerifier.Family binary prime P R cfg).compiler cfg.openingPositive).AcceptsIndexed
    (codec.withOracle (SHA ∘ merkleInput))
    ((Joint.Pair.statementEquiv _ _).symm decoded.statement.statement) (cfg.root key)
    ((Joint.Pair.coinEquiv _ _).symm decoded.coin)
    ((Joint.Pair.responseEquiv _ _).symm (RuntimeVerifier.responses binary prime P R cfg output.proof))
    decoded.query decoded.claim ∧
  finalSeal binary prime P R cfg earlier bodyCodec sample output SHA = output.proof.finalSeal ∧
  prefixZeros binary prime P R cfg output

def verify (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output) : Bool :=
  match RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
      (oracle binary prime P R cfg bodyCodec sample SHA) with
  | none => false
  | some decoded => decide (Checks binary prime P R cfg earlier bodyCodec sample codec SHA merkleInput output decoded)

theorem verify_true_iff (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output) :
    verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec SHA merkleInput output = true ↔
      ∃ decoded, RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
        (oracle binary prime P R cfg bodyCodec sample SHA) = some decoded ∧
          Checks binary prime P R cfg earlier bodyCodec sample codec SHA merkleInput output decoded := by
  unfold verify
  cases decoded : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
      (oracle binary prime P R cfg bodyCodec sample SHA) with
  | none => simp only [Bool.false_eq_true,reduceCtorEq,false_and,exists_false]
  | some value => simp only [decide_eq_true_eq,Option.some.injEq,exists_eq_left']

/-- Acceptance checks PRF counter zero of the reconstructed final node.
This supplies exactly the raw final-seal query obligation. -/
theorem accepted_seal (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output)
    (accepted : verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      SHA merkleInput output = true) :
    TranscriptV2.StrandVerifier.sealValid history sample cfg.fallback (M) output SHA := by
  obtain ⟨decoded,_,checks⟩ := (verify_true_iff binary prime P R cfg earlier bodyCodec sample
    hashPublic decodePublic draw codec SHA merkleInput output).mp accepted
  rw [TranscriptV2.StrandVerifier.sealValid_iff]
  exact checks.2.2.2.2.1

theorem accepted_samples (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output)
    (accepted : verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      SHA merkleInput output = true) :
    samplersSucceeded binary prime P R cfg earlier bodyCodec sample output SHA := by
  obtain ⟨_,_,checks⟩ := (verify_true_iff binary prime P R cfg earlier bodyCodec sample
    hashPublic decodePublic draw codec SHA merkleInput output).mp accepted
  exact checks.1

theorem reject_final_seal (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output)
    (wrong : finalSeal binary prime P R cfg earlier bodyCodec sample output SHA ≠ output.proof.finalSeal) :
    verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      SHA merkleInput output = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  obtain ⟨_,_,checks⟩ := (verify_true_iff binary prime P R cfg earlier bodyCodec sample
    hashPublic decodePublic draw codec SHA merkleInput output).mp accepted
  exact wrong checks.2.2.2.2.1

/-- Exhausting a physical sampler rejects even though mathematical replay
uses a dummy value to finish constructing its path. -/
theorem reject_failed_sample (SHA : Bytes → Digest) (merkleInput : Enc → Bytes) (output : Output)
    (i : Fin g.roles.length)
    (failed : ¬TranscriptV2.StrandVerifier.sampled history sample SHA
      ((M).point output (oracle binary prime P R cfg bodyCodec sample SHA) i.val)) :
    verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      SHA merkleInput output = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact failed (accepted_samples binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
    SHA merkleInput output accepted i)

/-- The concrete adaptive runtime's accepting decision forces the seal
query into the original raw search, except for seal guessing. Both the
requested public values and proof body may be adaptive. -/
theorem accepted_seal_query {fuel : ℕ} (search : Tree Bytes Digest Output fuel)
    (SHA : Bytes → Digest) (merkleInput : Enc → Bytes)
    (fits : g.roles.length < 2^64)
    (accepted : verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
      SHA merkleInput (search.run SHA).1 = true)
    (unguessed : ¬TranscriptV2.StrandSealCharging.Guess
      (TranscriptV2.StrandVerifier.sealModel history (M))
      (search.bind (TranscriptV2.StrandVerifier.beforeSeal history sample cfg.fallback (M))) SHA) :
    (TranscriptV2.StrandVerifier.sealModel history (M)).point
      ((search.bind (TranscriptV2.StrandVerifier.beforeSeal history sample cfg.fallback (M))).run SHA).1 SHA ∈
        TranscriptV2.seen search SHA := by
  apply StrandRuntime.seal_required bodyCodec (M) (fun _ => rfl)
    sample cfg.fallback search SHA fits unguessed
  exact accepted_seal binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
    SHA merkleInput (search.run SHA).1 accepted

end LfzkV2.Current.StrandVerifier
