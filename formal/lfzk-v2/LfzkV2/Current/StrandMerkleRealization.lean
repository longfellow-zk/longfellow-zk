import LfzkV2.Current.Format
import LfzkV2.Current.StrandCommitment
import TranscriptV2.CompositionTransport
import LfzkV2.Current.StrandRuntime
import LfzkV2.Current.StrandReplay
import LfzkV2.Current.StrandMerkleDomains

/-! Merkle extraction uses the actual byte codec. A finite query address
is only a name for those bytes; it is not a second codec with fallback leaf
or node encodings. Mapping a stopped cut preserves its order and answers. -/
noncomputable section
namespace LfzkV2.Current.StrandMerkleRealization
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand
open Merkle.MH (CollisionFree)
open scoped Classical

variable {Raw T Key Out : Type}

def byteName (bytes : Raw → Framing.Bytes) : StrandSearch.Name Raw T → StrandSearch.Name Framing.Bytes T
  | .inl (raw,value) => .inl (bytes raw,value)
  | .inr digest => .inr digest

/-- Reading child labels commutes with renaming the finite raw addresses. -/
theorem claims_bytes (readChildren : Framing.Bytes → Option (Digest × Digest))
    (bytes : Raw → Framing.Bytes) (context : T → Key) (root : Key → Digest) :
    StrandCommitment.claims readChildren context root ∘ byteName bytes =
      StrandCommitment.claims (readChildren ∘ bytes) context root := by
  funext point
  cases point with
  | inr _ => rfl
  | inl point =>
      rcases point with ⟨raw,value⟩
      cases value <;> rfl

/-- A logical name recovered by the actual online decoder encodes a
strand input. Its bytes therefore cannot also contribute Merkle children.
This discharges the root/children exclusivity premise of target charging. -/
theorem ordinary_no_children [DecidableEq Raw]
    (schema : History.Codec T) (bytes : Raw → Framing.Bytes) {fuel : ℕ}
    (program : Tree (StrandCoupling.Point Raw PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word)
    (raw : Raw) (value : T) (answer : StrandCoupling.Sample Digest Word)
    (member : ((.inl (raw,some value),answer) : StrandSearch.Name Raw T × _) ∈
      ((StrandReplay.search schema bytes program).run H).2) :
    MerkleWireCodec.nodeChildren (bytes raw) = none := by
  have named : FreshOracle.NamedTrace (StrandSearch.name schema bytes)
      (StrandSearch.advance bytes) StrandSearch.erase []
        ((StrandReplay.search schema bytes program).run H).2 := by
    simpa only [StrandReplay.search,StrandSearch.search,Tree.run_map] using
      StrandSearch.search_trace schema bytes (recordTrace program) H
  obtain ⟨first,rest,same⟩ := List.append_of_mem member
  have split := same ▸ named
  have decoded : StrandSearch.decode schema bytes
      (first.foldl (fun past qa => StrandSearch.advance bytes past (StrandSearch.erase qa.1) qa.2) []) raw =
      some value := (Prod.mk.inj (Sum.inl.inj split.name_after)).2
  rw [← StrandSearch.decode_erases schema bytes _ raw value decoded]
  exact StrandMerkleDomains.nodeChildren_input _

section Receiving
variable {Leaf Salt Point Challenge : Type} {valid : Point → Prop}
variable [DecidableEq Raw] [Fintype Raw] [Fintype T]
variable [Fintype Challenge] [Nonempty Challenge]
variable (codec : Codec Salt Leaf Digest Framing.Bytes)
variable (readChildren : Framing.Bytes → Option (Digest × Digest))
variable (bytes : Raw → Framing.Bytes) (context : T → Key) (root : Key → Digest)

/-- A receiving input is an actual Merkle leaf or internal-node preimage.
It need not be used by the eventual verifier; selecting that future subset
would destroy the stopped-prefix averaging argument. PRF addresses are absent. -/
def receives : StrandSearch.Name Raw T → Prop
  | .inl (raw,_) => (∃ leaf, bytes raw = codec.leafEnc leaf) ∨
      (∃ index children, bytes raw = codec.nodeEnc index children)
  | .inr _ => False

omit [DecidableEq Raw] [Fintype Raw] [Fintype T] in
/-- Canonical typed inputs and Merkle receiving inputs are disjoint.
This is a byte-codec fact, not a claim that all non-PRF inputs are auxiliary. -/
theorem receives_auxiliary
    (names : ByteOracleTransport.Codec Point (StrandSearch.Name Raw T) valid)
    (disjoint : ∀ point, ¬receives codec bytes (names.encode point))
    (raw : StrandSearch.Name Raw T) (receiving : receives codec bytes raw) :
    names.decode raw = none := by
  cases found : names.decode raw with
  | none => rfl
  | some point =>
      exact False.elim (disjoint point ((names.encode_decode raw point found).symm ▸ receiving))

end Receiving

section WireDomains
variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

/-- A Merkle input cannot plant a speculative strand parent or PRF key.
This is disjointness of literal input domains, not an oracle-output claim. -/
theorem receiving_claims_empty (bytes : Raw → Framing.Bytes) (point : StrandSearch.Name Raw T)
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes point) :
    StrandSearch.claims bytes point = ∅ := by
  cases point with
  | inr _ => exact False.elim receiving
  | inl point =>
      rcases point with ⟨raw,value⟩
      have rejected : Strand.Input.decode (bytes raw) = none := by
        cases found : Strand.Input.decode (bytes raw) with
        | none => rfl
        | some input =>
            have same := (Strand.Input.decode_sound (bytes raw) input found).2
            exfalso
            rcases receiving with ⟨leaf,encoded⟩ | ⟨index,children,encoded⟩
            · exact StrandMerkleDomains.input_ne_leaf P R repr binary prime context columnsFit
                input leaf (same.symm.trans encoded)
            · exact StrandMerkleDomains.input_ne_node P R repr binary prime context columnsFit
                input index children (same.symm.trans encoded)
      cases value <;> simp only [StrandSearch.claims,rejected]

/-- The concrete original-search charge covers a late authentication
query. Its target comes from the fixed root or an indexed node already in
the extraction cut; no future opening index is used in the charge itself. -/
theorem wire_late_query_charged [DecidableEq Raw]
    (schema : History.Codec T) (bytes : Raw → Framing.Bytes) (keyOf : T → Key) (root : Key → Digest)
    {fuel : ℕ} (program : Tree (StrandCoupling.Point Raw PrfKey Word) Digest Out fuel)
    (H : StrandSearch.Name Raw T → StrandCoupling.Sample Digest Word) (SHA : Framing.Bytes → Digest)
    (sound : ∀ raw logical answer,
      ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
        ((StrandReplay.search schema bytes program).run H).2 → answer.1 = SHA (bytes raw))
    (key : Key) (raw : Raw) (logical : Option T) (answer : StrandCoupling.Sample Digest Word)
    (queried : ((.inl (raw,logical),answer) : StrandSearch.Name Raw T × _) ∈
      ((StrandReplay.search schema bytes program).run H).2)
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes (.inl (raw,logical)))
    (missing : (bytes raw,answer.1) ∉
      (StrandCut.trace keyOf (StrandReplay.search schema bytes program) H key).map
        (fun qa => (bytes qa.1,qa.2)))
    (target : answer.1 = root key ∨ ∃ index input digest children,
      (input,digest) ∈ (StrandCut.trace keyOf (StrandReplay.search schema bytes program) H key).map
        (fun qa => (bytes qa.1,qa.2)) ∧
      (MerkleWireCodec.decoders P R repr binary prime context columnsFit).nodeDec index input = some children ∧
        (answer.1 = children.1 ∨ answer.1 = children.2)) :
    1 ≤ DigestProjection.receivingCharge
      (receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes)
      (StrandCommitment.claims MerkleWireCodec.nodeChildren keyOf root ∘ byteName bytes)
      (StrandReplay.search schema bytes program) H := by
  let tree := StrandReplay.search schema bytes program
  have value := sound raw logical answer queried
  rw [value] at missing target
  have absent : ∀ digest, (raw,digest) ∉ StrandCut.trace keyOf tree H key := by
    intro digest member
    obtain ⟨value,row,source⟩ := StrandCut.trace_source keyOf tree H key raw digest member
    rw [beforeLabel_eq_takeWhile] at source
    have correct := sound raw value (digest,row) ((List.takeWhile_sublist _).subset source)
    apply missing
    rw [← correct]
    exact List.mem_map_of_mem (f := fun qa => (bytes qa.1,qa.2)) member
  have hit : SHA (bytes raw) = root key ∨ ∃ input digest,
      (input,digest) ∈ StrandCut.trace keyOf tree H key ∧
        SHA (bytes raw) ∈ StrandCommitment.children (MerkleWireCodec.nodeChildren ∘ bytes) input := by
    rcases target with atRoot | ⟨index,input,digest,children,member,decoded,child⟩
    · exact Or.inl atRoot
    · obtain ⟨⟨source,result⟩,sourceMember,same⟩ := List.mem_map.mp member
      have sameInput : bytes source = input := congrArg Prod.fst same
      have read := MerkleWireCodec.nodeChildren_of_decoded P R repr binary prime context columnsFit
        index input children decoded
      refine Or.inr ⟨source,result,sourceMember,?_⟩
      simp only [StrandCommitment.children,Function.comp_apply,sameInput,read,
        Finset.mem_insert,Finset.mem_singleton]
      exact child
  have charged := StrandCommitment.missing_cut_hit (MerkleWireCodec.nodeChildren ∘ bytes) keyOf root tree H
    (SHA ∘ bytes) key raw logical answer queried value
    (ordinary_no_children schema bytes program H) absent hit
  rw [claims_bytes]
  exact DigestProjection.receiving_hit_charged _ _ tree H _ receiving charged

section RuntimeReceiving
variable {g : Geometry} {publicCount : ℕ} (fmt : Format g fields Advice publicCount)

variable (locate : fmt.Value → Raw)
variable (bytes : Raw → Framing.Bytes)
variable (located : ∀ value, bytes (locate value) =
  ((fmt.schema).encode value).input.encode)
include located

/-- The concrete codecs establish the auxiliary classification required
by the receiving mean, including arbitrary annotations on the raw name. -/
theorem wire_receives_auxiliary
    (raw : Raw) (value : Option (fmt.Value))
    (receiving : receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes (.inl (raw,value))) :
    (fmt.pointCodec locate).decode (.inl (raw,value)) = none := by
  apply fmt.pointCodec_merkle_auxiliary locate bytes located
  rcases receiving with ⟨leaf,equal⟩ | ⟨index,children,equal⟩
  · rw [equal]
    rfl
  · rw [equal]
    rfl

/-- The runtime codec's entire canonical image is outside the Merkle
receiving domain. No recognition, query-order, or hash assumption is needed. -/
theorem wire_receives_disjoint
    (point : {point // fmt.Canonical point}) :
    ¬receives (MerkleWireCodec.codec P R repr binary prime context columnsFit) bytes
      ((fmt.pointCodec locate).encode point) := by
  intro receiving
  have missing := wire_receives_auxiliary P R repr binary prime context columnsFit
    fmt locate bytes located _ _ receiving
  have decoded := (fmt.pointCodec locate).decode_encode point
  change (fmt.pointCodec locate).decode
    ((fmt.pointCodec locate).encode point) = none at missing
  have impossible := missing.symm.trans decoded
  cases impossible

end RuntimeReceiving

/-- Merkle leaf preimages begin with ASCII `p`; PRF preimages begin with
binary type word zero. This follows from the actual byte codec prefix. -/
theorem leaf_nonPrf (value : MerkleWireCodec.Salt n × (Joint.Pair.family P R).Leaf) :
    Strand.decodePrf ((MerkleWireCodec.leaf P R repr binary prime context columnsFit).encode value) = none := by
  cases found : Strand.decodePrf ((MerkleWireCodec.leaf P R repr binary prime context columnsFit).encode value) with
  | none => rfl
  | some address =>
      have encoded := Strand.decodePrf_sound _ address found
      have first := congrArg List.head? encoded
      change some (112 : Framing.Byte) = some (0 : Framing.Byte) at first
      exact False.elim ((by decide : (112 : Framing.Byte) ≠ 0) (Option.some.inj first))

/-- Internal Merkle nodes have the same explicit disjointness from PRF
inputs, independently of either child digest. -/
theorem node_nonPrf (index : ℕ) (children : Digest × Digest) :
    Strand.decodePrf ((MerkleWireCodec.node context index).encode children) = none := by
  cases found : Strand.decodePrf ((MerkleWireCodec.node context index).encode children) with
  | none => rfl
  | some address =>
      have encoded := Strand.decodePrf_sound _ address found
      have first := congrArg List.head? encoded
      change some (112 : Framing.Byte) = some (0 : Framing.Byte) at first
      exact False.elim ((by decide : (112 : Framing.Byte) ≠ 0) (Option.some.inj first))

end WireDomains
end LfzkV2.Current.StrandMerkleRealization
