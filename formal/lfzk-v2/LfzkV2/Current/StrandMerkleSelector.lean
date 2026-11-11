import LfzkV2.Current.StrandMerkleMissingQueries
import LfzkV2.Current.StrandRecordedReplay
import LfzkV2.Current.StrandMerkleDomains

/-! Select one disagreeing column using the actual ordered opening reader.
The submitted body fixes all column bytes and authentication data. The
reader fixes their positions. Comparing with the original-cut extraction
then needs no further oracle answer. The fallback only totalizes rejected
openings and claims whose columns already agree. -/
noncomputable section
namespace LfzkV2.Current.StrandMerkleSelector
open Merkle Merkle.Indexed TranscriptV2
open StrandMerkleMissingQueries
open scoped Classical

section Selection
variable {Salt Nonce Leaf D Enc C : Type} {n t : ℕ}
variable [DecidableEq D] [Inhabited Leaf]
variable (codec : Codec Salt Leaf D Enc) (dec : RoleDecoders codec)

def fromClaim (cut : List (Enc × D)) (root : D) (claim : MH.OpeningClaim n Salt Leaf D)
    (fallback : SelectedPath (Enc := Enc) (n := n) (Salt := Salt) (M := Leaf) (D := D)) :
    SelectedPath (Enc := Enc) (n := n) (Salt := Salt) (M := Leaf) (D := D) :=
  if different : ∃ column, column ∈ claim.I ∧ messages dec cut root n column ≠ claim.a column then
    { toOpeningClaim := claim
      root := root
      column := Classical.choose different
      opened := (Classical.choose_spec different).1
      cut := cut }
  else fallback

theorem fromClaim_spec (cut : List (Enc × D)) (root : D) (claim : MH.OpeningClaim n Salt Leaf D)
    (fallback : SelectedPath (Enc := Enc) (n := n) (Salt := Salt) (M := Leaf) (D := D))
    (different : ∃ column, column ∈ claim.I ∧ messages dec cut root n column ≠ claim.a column) :
    let path := fromClaim codec dec cut root claim fallback
    path.toOpeningClaim = claim ∧ path.root = root ∧ path.cut = cut ∧
      messages dec path.cut path.root n path.column ≠ path.a path.column := by
  dsimp only [fromClaim]
  rw [dif_pos different]
  exact ⟨rfl,rfl,rfl,(Classical.choose_spec different).2⟩

variable (bindSalt : Fin n → Nonce → Salt) (indices : C → (Fin t ↪ Fin n))
variable (fallbackChallenge : C) (raw : OrderedOpening.Raw t Nonce Leaf D)
variable (cut : List (Enc × D)) (root : D)
variable (fallbackPath : SelectedPath (Enc := Enc) (n := n) (Salt := Salt) (M := Leaf) (D := D))

def select (challenge : Option C) : SelectedPath (Enc := Enc) (n := n) (Salt := Salt) (M := Leaf) (D := D) :=
  match OrderedOpening.decode bindSalt (indices (challenge.getD fallbackChallenge)) raw with
  | none => fallbackPath
  | some claim => fromClaim codec dec cut root claim fallbackPath

theorem select_spec (challenge : Option C) (claim : MH.OpeningClaim n Salt Leaf D)
    (decoded : OrderedOpening.decode bindSalt (indices (challenge.getD fallbackChallenge)) raw = some claim)
    (different : ∃ column, column ∈ claim.I ∧ messages dec cut root n column ≠ claim.a column) :
    let path := select codec dec bindSalt indices fallbackChallenge raw cut root fallbackPath challenge
    path.toOpeningClaim = claim ∧ path.root = root ∧ path.cut = cut ∧
      messages dec path.cut path.root n path.column ≠ path.a path.column := by
  simp only [select,decoded]
  exact fromClaim_spec codec dec cut root claim fallbackPath different

end Selection

section Reader
variable {g : Geometry} {fields : Fields} {Advice Auth Key Fresh C : Type}
variable {capacity blocks : ℕ}
variable (bodyCodec : PrefixCodec (Body g fields Advice Auth))
variable (encoding : Replay.Encoding g fields Advice Auth Key (QueryRuntime.Block capacity Fresh) C)
variable (fallback : C) (proof : Replay.Output g fields Advice Auth) (trace : StrandRecordedReplay.Trace)
variable (sample : Replay.Point g fields Advice Auth Key (QueryRuntime.Block capacity Fresh) →
  Merkle.RandomOracle.Tree Strand.Word Digest (Option C) blocks)
variable (index : ℕ)

variable {k s n t : ℕ}
variable (P R : Joint.Participant k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)
local notation "codec" => MerkleWireCodec.codec P R repr binary prime context columnsFit
local notation "dec" => MerkleWireCodec.decoders P R repr binary prime context columnsFit

/-- The exact independence obligation of the missing-query bound. Any
postprocessing of this reader, including ordered decode and column selection,
inherits the equality. No Merkle answer is consulted to choose the path. -/
theorem read_merkle_off (H H' : Strand.Oracle) (raw : Bytes)
    (merkle : IsMerkleInput (codec) raw) (agree : Bcs.TotalOracle.AgreeOff raw H H') :
    StrandRecordedReplay.read bodyCodec encoding fallback proof trace sample H index =
      StrandRecordedReplay.read bodyCodec encoding fallback proof trace sample H' index := by
  apply StrandRecordedReplay.read_off bodyCodec encoding fallback proof trace sample H H' raw _ agree
  intro id digest counter
  rcases merkle with leaf | node
  · obtain ⟨value,rfl⟩ := leaf
    exact Ne.symm (StrandMerkleDomains.input_ne_leaf P R repr binary prime context columnsFit
      (.prf id digest counter) value)
  · obtain ⟨position,children,rfl⟩ := node
    exact Ne.symm (StrandMerkleDomains.input_ne_node P R repr binary prime context columnsFit
      (.prf id digest counter) position children)

variable [Inhabited (Joint.Pair.family P R).Leaf]
variable (indices : C → (Fin t ↪ Fin n))
variable (raw : OrderedOpening.Raw t MerkleNonce (Joint.Pair.family P R).Leaf Digest)
variable (cut : StrandRecordedReplay.Trace) (root : Digest)
variable (fallbackPath : SelectedPath (Enc := Bytes) (n := n) (Salt := MerkleWireCodec.Salt n)
  (M := (Joint.Pair.family P R).Leaf) (D := Digest))

def recordedSelect (H : Strand.Oracle) : SelectedPath (Enc := Bytes) (n := n)
    (Salt := MerkleWireCodec.Salt n) (M := (Joint.Pair.family P R).Leaf) (D := Digest) :=
  select (codec) (dec) (fun column nonce => (column,nonce)) indices fallback raw cut root fallbackPath
    (StrandRecordedReplay.read bodyCodec encoding fallback proof trace sample H index)

theorem recordedSelect_off (H H' : Strand.Oracle) (input : Bytes)
    (merkle : IsMerkleInput (codec) input) (agree : Bcs.TotalOracle.AgreeOff input H H') :
    recordedSelect bodyCodec encoding fallback proof trace sample index P R repr binary prime context columnsFit
        indices raw cut root fallbackPath H =
      recordedSelect bodyCodec encoding fallback proof trace sample index P R repr binary prime context columnsFit
        indices raw cut root fallbackPath H' := by
  unfold recordedSelect
  rw [read_merkle_off bodyCodec encoding fallback proof trace sample index
    P R repr binary prime context columnsFit H H' input merkle agree]

/-- Outside missing transcript nodes, the selected path belongs to the
same ordered opening that the actual verifier decodes. The only extra
choice is which disagreeing column to inspect in the soundness argument. -/
theorem recordedSelect_spec (initial : Digest) (H : Strand.Oracle)
    (independent : ∀ i first second, encoding.block proof i first = encoding.block proof i second)
    (sound : ∀ entry ∈ trace, H entry.1 = entry.2)
    (known : ∀ i ≤ index, ∃ digest,
      ((StrandRuntime.history bodyCodec ((encoding.chain initial).point proof
        (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback H) i)).input.encode,
        digest) ∈ trace)
    (claim : MH.OpeningClaim n (MerkleWireCodec.Salt n) (Joint.Pair.family P R).Leaf Digest)
    (decoded : OrderedOpening.decode (fun column nonce => (column,nonce))
      (indices ((TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback H)
        ((encoding.chain initial).point proof
          (TranscriptV2.StrandVerifier.oracle (StrandRuntime.history bodyCodec) sample fallback H) index)).2)
      raw = some claim)
    (different : ∃ column, column ∈ claim.I ∧ messages (dec) cut root n column ≠ claim.a column) :
    let path := recordedSelect bodyCodec encoding fallback proof trace sample index
      P R repr binary prime context columnsFit indices raw cut root fallbackPath H
    path.toOpeningClaim = claim ∧ path.root = root ∧ path.cut = cut ∧
      messages (dec) path.cut path.root n path.column ≠ path.a path.column := by
  apply select_spec (codec) (dec) (fun column nonce => (column,nonce)) indices fallback raw cut root fallbackPath
  · rw [StrandRecordedReplay.read_eq bodyCodec encoding fallback proof trace sample initial independent
      H index sound known]
    exact decoded
  · exact different

end Reader
end LfzkV2.Current.StrandMerkleSelector
