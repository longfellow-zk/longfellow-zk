import LfzkV2.Current.StrandMerkleSelector
import LfzkV2.Current.Soundness.OracleBounds

/-! Apply the one-column authentication bound to the actual canonical
runtime. The selected column is read using the recorded transcript nodes
and actual PRF sampler. The original finite query table determines the cut;
the verifier's authentication queries do not enlarge its query budget. -/
noncomputable section
namespace LfzkV2.Current.StrandMerkleBounds
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open StrandMerkleMissingQueries
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits k s n t blocks : ℕ}
variable [Inhabited (Fin n × MerkleNonce)]
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin n × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (fits : g.roles.length < 2^64) (columnsFit : n ≤ 2^64)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)
local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R (W)
local notation "Second" => RuntimeVerifier.second binary prime P R (W)
local notation "Family" => Joint.Pair.family (FieldBackend.participant (First)) (FieldBackend.participant (Second))
local notation "codec" => MerkleWireCodec.codec (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
  cfg.binaryField cfg.primeField setup.jointContext columnsFit
local notation "dec" => MerkleWireCodec.decoders (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
  cfg.binaryField cfg.primeField setup.jointContext columnsFit
variable [leafDefault : Inhabited
  (Joint.Pair.family (P.indexed cfg.countBinary).participant (R.indexed cfg.countPrime).participant).Leaf]
local instance runtimeLeafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R
    (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf := by
  change Inhabited
    (Joint.Pair.family (P.indexed cfg.countBinary).participant (R.indexed cfg.countPrime).participant).Leaf
  exact leafDefault
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "E" => RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier)
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "schema" => StrandRuntime.Runtime.schema repr shape setup binary.nPublic
local notation "context" => QueryRuntime.Runtime.key repr shape setup binary.nPublic
variable {fuel : ℕ} (program : Merkle.RandomOracle.Tree Bytes Digest
  (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)
local notation "O" => Soundness.OracleTransport.other binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "Node" => StrandWindow.Node (O)
local notation "Raw" => StrandWindow.Point (O)
local notation "fallbackNode" => Soundness.OracleTransport.fallback binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "decodeRaw" => StrandWindow.decode (O) fallbackNode
local notation "bytes" => StrandWindow.Node.bytes (other := O)
local notation "compiled" => mapQueries decodeRaw program
local notation "Path" => SelectedPath (n := n) (Salt := Fin n × MerkleNonce) (M := (Joint.Family.Leaf (Family)))
  (D := Digest) (Enc := Bytes)

/-- Recover the same first-context cut from the original query table.
Its answer at the commitment boundary is deliberately excluded. -/
def cut (result : Output × List (Raw × Digest)) : List (Bytes × Digest) :=
  StrandCutObservation.byteCut (schema) bytes context ((E result.1.request).context result.1.proof) result.2

theorem cut_subset (result : Output × List (Raw × Digest)) :
    cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program result ⊆
      result.2.map (fun qa => (StrandWindow.encode qa.1,qa.2)) := by
  intro entry member
  obtain ⟨⟨raw,digest⟩,present,rfl⟩ := List.mem_map.mp member
  have source := StrandCutObservation.scan_mem (schema) bytes context
    ((E result.1.request).context result.1.proof)
    (StrandCoupling.Cache.empty : StrandCoupling.Cache Node Strand.PrfKey Digest Strand.Word).nodes
    [] result.2 raw digest present
  exact List.mem_map.mpr ⟨(.inl raw,digest),source,rfl⟩

variable (fallbackPath : SelectedPath (n := n) (Salt := Fin n × MerkleNonce)
  (M := (Joint.Pair.family (P.indexed cfg.countBinary).participant (R.indexed cfg.countPrime).participant).Leaf)
  (D := Digest) (Enc := Bytes))

/-- The actual ordered opening reader, followed by selection of one
column disagreeing with the original-cut extraction. Only the rejected or
already-agreeing cases use the irrelevant fallback path. -/
def selected (result : Output × List (Raw × Digest)) (SHA : Strand.Oracle) : Path :=
  StrandMerkleSelector.recordedSelect bodyCodec (E result.1.request) cfg.fallback result.1.proof
    (result.2.map fun qa => (StrandWindow.encode qa.1,qa.2)) sample g.openingIndex
    (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr cfg.binaryField cfg.primeField setup.jointContext columnsFit
    cfg.sample
    (OpeningBody.raw (FieldBackend.participant (First)) (FieldBackend.participant (Second)) cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings result.1.proof)
    (cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program result)
    ((W).root ((E result.1.request).context result.1.proof)) fallbackPath SHA

theorem selected_off (result : Output × List (Raw × Digest)) (SHA SHA' : Strand.Oracle)
    (input : Bytes) (merkle : IsMerkleInput (codec) input)
    (agree : Bcs.TotalOracle.AgreeOff input SHA SHA') :
    selected binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program fallbackPath result SHA =
      selected binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program fallbackPath result SHA' := by
  unfold selected StrandMerkleSelector.recordedSelect
  apply congrArg
  apply StrandRecordedReplay.read_off _ _ _ _ _ _ SHA SHA' input _ agree
  intro id digest counter
  rcases merkle with leaf | node
  · obtain ⟨value,rfl⟩ := leaf
    exact Ne.symm (StrandMerkleDomains.input_ne_leaf (FieldBackend.participant (First))
      (FieldBackend.participant (Second)) repr cfg.binaryField cfg.primeField setup.jointContext columnsFit
      (.prf id digest counter) value)
  · obtain ⟨index,children,rfl⟩ := node
    exact Ne.symm (StrandMerkleDomains.input_ne_node (FieldBackend.participant (First))
      (FieldBackend.participant (Second)) repr cfg.binaryField cfg.primeField setup.jointContext columnsFit
      (.prf id digest counter) index children)

/-- A represented Merkle input has one raw preimage. The only address
that aliases out-of-window inputs is a strand root, in a disjoint domain. -/
theorem merkle_fiber (input : Bytes) (merkle : IsMerkleInput (codec) input)
    (represented : StrandWindow.encode (decodeRaw input) = input)
    (other : Bytes) (same : decodeRaw other = decodeRaw input) : other = input := by
  have distinct : decodeRaw input ≠ .inl fallbackNode := by
    intro equal
    have bad : (Strand.Input.root []).encode = input := by
      rw [equal] at represented
      exact represented
    rcases merkle with leaf | node
    · obtain ⟨value,rfl⟩ := leaf
      exact StrandMerkleDomains.input_ne_leaf (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
        cfg.binaryField cfg.primeField setup.jointContext columnsFit (.root []) value bad
    · obtain ⟨index,children,rfl⟩ := node
      exact StrandMerkleDomains.input_ne_node (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
        cfg.binaryField cfg.primeField setup.jointContext columnsFit (.root []) index children bad
  exact (StrandWindow.decode_fiber (O) fallbackNode (decodeRaw input) distinct other same).trans represented

local notation "choose" => selected binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit
  sample program fallbackPath

/-- This event uses the submitted proof and the original query table.
The table is recorded once for selection, without changing any query. -/
def freshHit (G : Raw → Digest) : Prop :=
  ∃ slot, UnqueriedAnswer.PartialHit
    (fun result H => restrictedChosen (codec) (dec) choose
      StrandWindow.encode decodeRaw result H slot)
    (recordTrace compiled) G

/-- The existing one-path estimate instantiated with the runtime's actual
SHA reader, indexed tuple codec, and original finite query table. -/
theorem freshHit_ratio_le :
    density (freshHit binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit
      sample program fallbackPath) ≤ (Heap.heapDepth n+1 : ℚ) / 2^256 := by
  have bound := restricted_any_hit_density_le (codec) (dec)
    choose
    (MerkleWireCodec.separated (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
      cfg.binaryField cfg.primeField setup.jointContext columnsFit)
    (by
      intro result SHA SHA' input merkle agree
      exact selected_off binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit
        sample program fallbackPath result SHA SHA' input merkle agree)
    StrandWindow.encode decodeRaw
    (merkle_fiber binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program)
    (recordTrace compiled)
  have size : (Fintype.card Digest : ℚ) = 2^256 := by
    rw [Strand.digest_card,Nat.cast_pow,Nat.cast_ofNat]
  exact bound.trans_eq (by rw [size])

variable (independent : CanonicalRequest.ChallengeIndependent shape binary.nPublic metadata)
variable (bindSalt : ∀ key column nonce, cfg.bindSalt key column nonce = (column,nonce))
variable (primeCount : shape.primePublic = prime.nPublic)
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg))
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "ordinary" => StrandVerifier.oracle binary prime P R (W) bodyCodec sample
local notation "hashPublic" => CanonicalRequest.hashPublic binary.nPublic
local notation "primePublic" => CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount

include independent bindSalt in
/-- Once the original table contains the transcript nodes, selection is
from precisely the opening accepted by the actual runtime decoder. The
claim, root and extraction cut are all equal, not merely related by a
separate semantic verifier. -/
theorem selected_spec (G : Raw → Digest)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W))
    (decodedAt : RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      hashPublic primePublic draw ((compiled).run G).1 (ordinary (G ∘ decodeRaw)) = some decoded)
    (known : ∀ i ≤ g.openingIndex.val, QueryTable.Known
      (((compiled).run G).2.map fun qa => (StrandWindow.encode qa.1,qa.2))
      (StrandRuntime.history bodyCodec ((M).point ((compiled).run G).1 (ordinary (G ∘ decodeRaw)) i)).input.encode)
    (different : ∃ column, column ∈ decoded.claim.I ∧
      messages (dec)
        (cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program ((compiled).run G))
        ((W).root ((E ((compiled).run G).1.request).context ((compiled).run G).1.proof)) n column ≠
          decoded.claim.a column) :
    let path := choose ((compiled).run G) (G ∘ decodeRaw)
    path.toOpeningClaim = decoded.claim ∧
      path.root = (W).root ((E ((compiled).run G).1.request).context ((compiled).run G).1.proof) ∧
      path.cut = cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program ((compiled).run G) ∧
      messages (dec) path.cut path.root n path.column ≠ path.a path.column := by
  let result := (compiled).run G
  have sound : ∀ entry ∈ result.2.map (fun qa => (StrandWindow.encode qa.1,qa.2)),
      (G ∘ decodeRaw) entry.1 = entry.2 := by
    intro entry member
    obtain ⟨⟨input,answer⟩,present,rfl⟩ := List.mem_map.mp member
    rw [Function.comp_apply,StrandWindow.decode_encode]
    exact (Tree.trace_sound compiled G _ present).symm
  have blocksIndependent : ∀ i first second,
      (E result.1.request).block result.1.proof i first = (E result.1.request).block result.1.proof i second := by
    rw [CanonicalRuntime.encodings_eq]
    exact CanonicalRequest.block_challengeIndependent repr shape setup binary.nPublic
      (CanonicalRuntime.binaryRequest binary prime P R repr shape setup cfg binaryCount)
      metadata independent result.1.request result.1.proof
  have openingDecoded := (RuntimeAdaptiveVerifier.decode_spec binary prime P R (W) (Earlier)
    hashPublic primePublic draw result.1 (ordinary (G ∘ decodeRaw)) decoded decodedAt).2.1
  have salts : (W).bindSalt ((E result.1.request).context result.1.proof) =
      fun column nonce => (column,nonce) := by
    funext column nonce
    exact bindSalt _ column nonce
  rw [salts] at openingDecoded
  apply StrandMerkleSelector.recordedSelect_spec bodyCodec (E result.1.request) cfg.fallback result.1.proof
    (result.2.map fun qa => (StrandWindow.encode qa.1,qa.2)) sample g.openingIndex
    (FieldBackend.participant (First)) (FieldBackend.participant (Second)) repr
    cfg.binaryField cfg.primeField setup.jointContext columnsFit cfg.sample _ _ _ fallbackPath
    cfg.initialLink (G ∘ decodeRaw) blocksIndependent sound _ decoded.claim openingDecoded different
  intro i within
  have present := known i within
  rw [RuntimeAdaptiveVerifier.point_eq] at present
  exact present

/-- A selected path from the decoded claim uses addresses covered by the
actual verifier continuation. Rejected fallback paths need no such claim. -/
theorem path_represented (G : Raw → Digest)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W))
    (decodedAt : RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      hashPublic primePublic draw ((compiled).run G).1 (ordinary (G ∘ decodeRaw)) = some decoded)
    (path : Path) (sameClaim : path.toOpeningClaim = decoded.claim)
    (slot : Fin (Heap.heapDepth n+1)) :
    StrandWindow.encode (decodeRaw (point (codec) path (G ∘ decodeRaw) slot)) =
      point (codec) path (G ∘ decodeRaw) slot := by
  have opened : path.column ∈ decoded.claim.I := by
    rw [← sameClaim]
    exact path.opened
  have visible := StrandAuthentication.decoded_path_visible binary prime P R (W) (Earlier)
    bodyCodec sample (codec) id hashPublic primePublic draw ((compiled).run G).1 (G ∘ decodeRaw)
    decoded decodedAt path.column opened (vertex path slot) (vertex_mem path slot)
  have inputEq := claim_pathInput_congr (codec) path.toOpeningClaim decoded.claim
    sameClaim path.column path.opened opened (G ∘ decodeRaw) (vertex path slot)
  simp only [Function.comp_id,id_eq,← inputEq] at visible
  apply Soundness.OracleTransport.input_represented binary prime P R repr shape setup cfg binaryCount metadata
    fits sample (codec) id program
  apply OracleWindow.trace_mem_queries (program.bind
    (StrandAuthentication.replay binary prime P R (W) (Earlier) bodyCodec sample (codec) id))
    (G ∘ decodeRaw) (point (codec) path (G ∘ decodeRaw) slot,G (decodeRaw (point (codec) path (G ∘ decodeRaw) slot)))
  rw [Tree.run_bind]
  apply List.mem_append_right
  have outputEq := congrArg Prod.fst (Soundness.OracleTransport.original_actual binary prime P R repr shape setup cfg
    binaryCount metadata fits sample (codec) id program G)
  change ((compiled).run G).1 = (program.run (G ∘ decodeRaw)).1 at outputEq
  rw [← outputEq]
  exact visible

include independent bindSalt in
/-- Outside the transcript exception, an authenticated column mismatch
is either already present after the original commitment cut, or is the
fresh path event bounded above. Authentication does not add to the original
query budget. -/
theorem accepted_cover (G : Raw → Digest)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W))
    (decodedAt : RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      hashPublic primePublic draw ((compiled).run G).1 (ordinary (G ∘ decodeRaw)) = some decoded)
    (known : ∀ i ≤ g.openingIndex.val, QueryTable.Known
      (((compiled).run G).2.map fun qa => (StrandWindow.encode qa.1,qa.2))
      (StrandRuntime.history bodyCodec ((M).point ((compiled).run G).1 (ordinary (G ∘ decodeRaw)) i)).input.encode)
    (unique : Merkle.MH.CollisionFree
      (((compiled).run G).2.map fun qa => (StrandWindow.encode qa.1,qa.2)))
    (accepted : Merkle.Indexed.Accepts ((codec).withOracle (G ∘ decodeRaw)) n
      ((W).root ((E ((compiled).run G).1.request).context ((compiled).run G).1.proof))
      decoded.claim.I decoded.claim.a decoded.claim.pf)
    (different : ∃ column, column ∈ decoded.claim.I ∧
      messages (dec)
        (cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program ((compiled).run G))
        ((W).root ((E ((compiled).run G).1.request).context ((compiled).run G).1.proof)) n column ≠
          decoded.claim.a column) :
    OriginalHit (codec) (dec)
      (((compiled).run G).2.map fun qa => (StrandWindow.encode qa.1,qa.2))
      (cut binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program ((compiled).run G))
      ((W).root ((E ((compiled).run G).1.request).context ((compiled).run G).1.proof)) ∨
    freshHit binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program fallbackPath G := by
  let result := (compiled).run G
  let path := choose result (G ∘ decodeRaw)
  have spec := selected_spec binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample
    program fallbackPath independent bindSalt primeCount draw G decoded decodedAt known different
  have represented := fun slot => path_represented binary prime P R repr shape setup cfg binaryCount metadata
    fits columnsFit sample program primeCount draw G decoded decodedAt path spec.1 slot
  have cutUnique : Merkle.MH.CollisionFree path.cut := by
    rw [spec.2.2.1]
    intro first hf second hs eq
    exact unique first
      (cut_subset binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program result hf)
      second (cut_subset binary prime P R repr shape setup cfg binaryCount metadata fits columnsFit sample program result hs) eq
  have pathAccepted : Merkle.Indexed.Accepts ((codec).withOracle (G ∘ decodeRaw)) n
      path.root path.I path.a path.pf := by
    change Merkle.Indexed.Accepts _ n path.root path.toOpeningClaim.I path.toOpeningClaim.a path.toOpeningClaim.pf
    rw [spec.1,spec.2.1]
    exact accepted
  have cover := disagreement_restricted_cover (codec) (dec) choose
    StrandWindow.encode decodeRaw (recordTrace compiled) G
    (by simpa only [run_recordTrace] using represented)
    (by simpa only [run_recordTrace] using cutUnique)
    (by dsimp only; rw [run_recordTrace]; exact pathAccepted)
    (by simpa only [run_recordTrace] using spec.2.2.2)
  rcases cover with old | fresh
  · exact Or.inl (by simpa only [run_recordTrace,spec.2.1,spec.2.2.1] using old)
  · exact Or.inr fresh

end LfzkV2.Current.StrandMerkleBounds
