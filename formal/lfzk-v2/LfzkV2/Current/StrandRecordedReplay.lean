import LfzkV2.Current.StrandSealIndependence
import Merkle.QueryTable

/-! Recover an opening reader from the submitted proof and original query
table. Replaying recorded node answers makes no fresh hash queries. Once
the missing-node event is excluded, it gives the actual verifier's point
and digest, even if the prover queried those nodes out of protocol order.
Only the reader then consults the oracle, exclusively in the PRF domain. -/
namespace LfzkV2.Current.StrandRecordedReplay
open CanonicalPrefix QueryRuntime TranscriptV2 Merkle.RandomOracle

abbrev Trace := List (Bytes × Digest)

def recorded (trace : Trace) : Strand.Oracle :=
  fun raw => (Merkle.QueryTable.answer trace raw).getD (fun _ => 0)

theorem recorded_eq (trace : Trace) (H : Strand.Oracle)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2) (raw : Bytes)
    (known : ∃ digest, (raw,digest) ∈ trace) : recorded trace raw = H raw := by
  unfold recorded
  rw [Merkle.QueryTable.answer_of_mem trace H sound raw known]
  rfl

section Replay
variable {g : Geometry} {fields : Fields} {Advice Auth Key Fresh C : Type}
variable {capacity blocks : ℕ}
variable (bodyCodec : PrefixCodec (Body g fields Advice Auth))
variable (encoding : Replay.Encoding g fields Advice Auth Key (Block capacity Fresh) C)
variable (fallback : C) (proof : Replay.Output g fields Advice Auth) (trace : Trace)

def point (index : ℕ) : Replay.Point g fields Advice Auth Key (Block capacity Fresh) :=
  (encoding.transcript proof fallback).replay
    (fun current => recorded trace (StrandRuntime.history bodyCodec current).input.encode) index

variable (sample : Replay.Point g fields Advice Auth Key (Block capacity Fresh) →
  Tree Strand.Word Digest (Option C) blocks)

/-- Both the reader program and its PRF key are fixed by the proof and
recorded table. Failure remains `none`; no successful sampling is assumed. -/
def read (H : Strand.Oracle) (index : ℕ) : Option C :=
  let current := point bodyCodec encoding fallback proof trace index
  let history := StrandRuntime.history bodyCodec current
  ((sample current).run (fun counter =>
    H (Strand.Input.prf history.id (recorded trace history.input.encode) counter).encode)).1

theorem read_congr (H H' : Strand.Oracle)
    (prfs : ∀ id digest counter,
      H (Strand.Input.prf id digest counter).encode =
        H' (Strand.Input.prf id digest counter).encode) (index : ℕ) :
    read bodyCodec encoding fallback proof trace sample H index =
      read bodyCodec encoding fallback proof trace sample H' index := by
  have same (id : Strand.Word) (digest : Digest) :
      (fun counter => H (Strand.Input.prf id digest counter).encode) =
        (fun counter => H' (Strand.Input.prf id digest counter).encode) := funext (prfs id digest)
  dsimp only [read]
  rw [same]

theorem read_off (H H' : Strand.Oracle) (raw : Bytes)
    (nonPrf : ∀ id digest counter, raw ≠ (Strand.Input.prf id digest counter).encode)
    (agree : Bcs.TotalOracle.AgreeOff raw H H') (index : ℕ) :
    read bodyCodec encoding fallback proof trace sample H index =
      read bodyCodec encoding fallback proof trace sample H' index := by
  apply read_congr
  intro id digest counter
  exact agree _ (Ne.symm (nonPrf id digest counter))

variable (initial : Digest)
variable (independent : ∀ i first second, encoding.block proof i first = encoding.block proof i second)
local notation "oracle" => TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback

include independent in
theorem point_eq (H : Strand.Oracle) (index : ℕ)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2)
    (known : ∀ i < index, ∃ digest,
      ((StrandRuntime.history bodyCodec ((encoding.chain initial).point proof (oracle H) i)).input.encode,digest) ∈ trace) :
    (encoding.chain initial).point proof (oracle H) index = point bodyCodec encoding fallback proof trace index := by
  rw [encoding.replay_transcript proof fallback independent]
  apply Replay.Transcript.replay_congr_on_prefix
  intro i earlier
  rw [← encoding.replay_transcript proof fallback independent initial (oracle H) i]
  rw [TranscriptV2.StrandVerifier.oracle_node]
  exact (recorded_eq trace H sound _ (known i earlier)).symm

include independent in
/-- The recovered reader returns the verifier's actual challenge. The
premise is exactly that its prefix and current node occur in the original
trace; it requires neither their chronological order nor distinct digests. -/
theorem read_eq (H : Strand.Oracle) (index : ℕ)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2)
    (known : ∀ i ≤ index, ∃ digest,
      ((StrandRuntime.history bodyCodec ((encoding.chain initial).point proof (oracle H) i)).input.encode,digest) ∈ trace) :
    (read bodyCodec encoding fallback proof trace sample H index).getD fallback =
      (oracle H ((encoding.chain initial).point proof (oracle H) index)).2 := by
  have same := point_eq bodyCodec encoding fallback proof trace sample initial independent H index
    sound (fun i earlier => known i (by omega))
  dsimp only [read]
  rw [← same,recorded_eq trace H sound _ (known index le_rfl)]
  exact (TranscriptV2.StrandVerifier.oracle_challenge _ _ _ _ _).symm

end Replay

section Runtime
open Application ApplicationSetup
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
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "oracle" => StrandVerifier.oracle binary prime P R (W) bodyCodec sample

/-- This uses the same canonical request and complete proof encoder as
the runtime. Only node answers are replaced by original-table lookups. -/
def runtimeRead (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (trace : Trace) (H : Strand.Oracle) (index : ℕ) : Option C :=
  read bodyCodec (Earlier output.request) cfg.fallback output.proof trace sample H index

include independent in
theorem runtimeRead_eq (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (trace : Trace) (H : Strand.Oracle) (index : ℕ)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2)
    (known : ∀ i ≤ index, ∃ digest,
      ((StrandRuntime.history bodyCodec ((M).point output (oracle H) i)).input.encode,digest) ∈ trace) :
    (runtimeRead binary prime P R repr shape setup cfg binaryCount metadata sample output trace H index).getD
        cfg.fallback = (oracle H ((M).point output (oracle H) index)).2 := by
  simp only [RuntimeAdaptiveVerifier.point_eq,CanonicalRuntime.encodings_eq] at known ⊢
  apply read_eq bodyCodec (Earlier output.request) cfg.fallback output.proof trace sample cfg.initialLink
    _ H index sound known
  exact CanonicalRequest.block_challengeIndependent repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
    metadata independent output.request output.proof

omit [DecidableEq B] in
theorem runtimeRead_off (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (trace : Trace) (H H' : Strand.Oracle) (raw : Bytes)
    (nonPrf : ∀ id digest counter, raw ≠ (Strand.Input.prf id digest counter).encode)
    (agree : Bcs.TotalOracle.AgreeOff raw H H') (index : ℕ) :
    runtimeRead binary prime P R repr shape setup cfg binaryCount metadata sample output trace H index =
      runtimeRead binary prime P R repr shape setup cfg binaryCount metadata sample output trace H' index :=
  read_off bodyCodec (Earlier output.request) cfg.fallback output.proof trace sample H H' raw nonPrf agree index

end Runtime
end LfzkV2.Current.StrandRecordedReplay
