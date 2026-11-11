import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.StrandVerifier
import LfzkV2.Current.StrandLinearReplay

/-! A fixed submitted proof determines its absorbed packets independently
of challenges. Replay therefore separates into a transcript driven only by
node hashes and a verifier cache used for arithmetic. In particular, PRF
answers cannot affect the final-seal address, even when node hashes collide. -/
noncomputable section
namespace LfzkV2.Current.StrandSealIndependence
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Merkle.RandomOracle TranscriptV2
open scoped Classical

section Replay
variable {g : Geometry} {fields : Fields} {Advice Auth Key Fresh C : Type}
variable {capacity blocks : ℕ}
variable (bodyCodec : PrefixCodec (Body g fields Advice Auth))
variable (encoding : Replay.Encoding g fields Advice Auth Key (Block capacity Fresh) C)
variable (sample : Replay.Point g fields Advice Auth Key (Block capacity Fresh) →
  Tree Strand.Word Digest (Option C) blocks) (initial : Digest)

/-- Only the transcript projection is compared. The two verifier caches
may hold completely different challenges. -/
theorem point_nodes_congr (default : C) (proof : Replay.Output g fields Advice Auth)
    (independent : ∀ i first second, encoding.block proof i first = encoding.block proof i second)
    (G G' : Strand.Oracle)
    (nodes : ∀ history : Strand.History, G history.input.encode = G' history.input.encode)
    (index : ℕ) :
    (encoding.chain initial).point proof
        (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample default G) index =
      (encoding.chain initial).point proof
        (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample default G') index := by
  rw [encoding.replay_transcript proof default independent,
    encoding.replay_transcript proof default independent]
  have same : (fun point =>
      (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample default G point).1) =
      (fun point =>
        (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample default G' point).1) := by
    funext point
    rw [TranscriptV2.StrandVerifier.oracle_node,TranscriptV2.StrandVerifier.oracle_node]
    exact nodes _
  rw [same]

end Replay

section Runtime
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
local notation "address" => StrandVerifier.finalSealAddress binary prime P R (W) (Earlier) bodyCodec sample

include independent in
theorem runtime_point_congr (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (G G' : Strand.Oracle)
    (nodes : ∀ history : Strand.History, G history.input.encode = G' history.input.encode)
    (index : ℕ) :
    (M).point output (oracle G) index = (M).point output (oracle G') index := by
  rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveVerifier.point_eq,
    CanonicalRuntime.encodings_eq]
  apply point_nodes_congr bodyCodec (Earlier output.request) sample cfg.initialLink cfg.fallback output.proof
  · exact CanonicalRequest.block_challengeIndependent repr shape setup binary.nPublic
      (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
      metadata independent output.request output.proof
  · exact nodes

include independent in
/-- The actual request/proof encoder supplies the packets in the numbered
linear chain. Neither field challenges nor reconstructed adapter coefficients
occur in this packet function. -/
theorem runtime_history_replay (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (G : Strand.Oracle) (index : ℕ) (within : index ≤ g.roles.length) :
    StrandRuntime.history bodyCodec ((M).point output (oracle G) index) =
      StrandLinear.replay
        (StrandLinearReplay.packets bodyCodec (Earlier output.request) cfg.fallback output.proof)
        G index := by
  rw [RuntimeAdaptiveVerifier.point_eq,CanonicalRuntime.encodings_eq]
  apply StrandLinearReplay.history_replay bodyCodec (Earlier output.request) cfg.fallback output.proof
    _ cfg.initialLink sample G index within
  exact CanonicalRequest.block_challengeIndependent repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
    metadata independent output.request output.proof

include independent in
/-- The address of the complete-proof seal depends only on node answers,
not on any PRF answer. No injectivity or collision exception is needed. -/
theorem finalSealAddress_congr (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (G G' : Strand.Oracle)
    (nodes : ∀ history : Strand.History, G history.input.encode = G' history.input.encode) :
    address output G = address output G' := by
  have point := runtime_point_congr binary prime P R repr shape setup cfg binaryCount metadata
    independent sample output G G' nodes g.roles.length
  unfold StrandVerifier.finalSealAddress
  change (Strand.Input.prf
      (StrandRuntime.history bodyCodec ((M).point output (oracle G) g.roles.length)).id
      (G (StrandRuntime.history bodyCodec ((M).point output (oracle G) g.roles.length)).input.encode) 0).encode = _
  rw [point,nodes]
  rfl

include independent in
/-- Changing the seal's own PRF answer leaves its address unchanged. This
remains true if a verifier sampler happens to read that same PRF block. -/
theorem finalSealAddress_off (output : CanonicalRuntime.Output (Advice := Advice) binary shape)
    (G G' : Strand.Oracle) (agree : Bcs.TotalOracle.AgreeOff (address output G) G G') :
    address output G = address output G' := by
  apply finalSealAddress_congr binary prime P R repr shape setup cfg binaryCount metadata independent sample
  intro history
  apply agree
  exact history.input_ne_prf _ _ 0

end Runtime
end LfzkV2.Current.StrandSealIndependence
