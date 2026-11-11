import LfzkV2.Current.StrandMerkleRealization

namespace LfzkV2.Current.Tests.StrandMerkleReceiving
open TranscriptV2 TranscriptV2.Strand Merkle.Indexed

-- A PRF row cannot be a receiving Merkle input, regardless of its digest.
example {Raw T Salt Leaf : Type} (codec : Codec Salt Leaf Digest Framing.Bytes)
    (bytes : Raw → Framing.Bytes) (digest : PrfKey) :
    ¬StrandMerkleRealization.receives (T := T) codec bytes (.inr digest) := by
  exact id

-- Both actual Merkle preimage roles are counted; logical annotations do
-- not hide a receiving query from the charge.
example {Raw T Salt Leaf : Type} (codec : Codec Salt Leaf Digest Framing.Bytes)
    (bytes : Raw → Framing.Bytes) (raw : Raw) (value : Option T) (leaf : Salt × Leaf)
    (encoded : bytes raw = codec.leafEnc leaf) :
    StrandMerkleRealization.receives codec bytes (.inl (raw,value)) := Or.inl ⟨leaf,encoded⟩

example {Raw T Salt Leaf : Type} (codec : Codec Salt Leaf Digest Framing.Bytes)
    (bytes : Raw → Framing.Bytes) (raw : Raw) (value : Option T) (index : ℕ) (children : Digest × Digest)
    (encoded : bytes raw = codec.nodeEnc index children) :
    StrandMerkleRealization.receives codec bytes (.inl (raw,value)) := Or.inr ⟨index,children,encoded⟩

/--
info: 'LfzkV2.Current.StrandRuntime.Runtime.pointCodec_merkle_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandRuntime.Runtime.pointCodec_merkle_auxiliary

/--
info: 'LfzkV2.Current.StrandMerkleRealization.receiving_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandMerkleRealization.receiving_sum_le

/--
info: 'LfzkV2.Current.StrandMerkleRealization.wire_receives_disjoint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandMerkleRealization.wire_receives_disjoint

/--
info: 'LfzkV2.Current.StrandMerkleRealization.wire_receiving_sum_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandMerkleRealization.wire_receiving_sum_le

#guard_msgs (drop info) in #check StrandMerkleRealization.receives_tag
#guard_msgs (drop info) in #check DigestProjection.receiving_hit_charged

/--
info: 'LfzkV2.Current.StrandMerkleRealization.wire_hash_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
set_option pp.fullNames true in
#print axioms StrandMerkleRealization.wire_hash_sum_le

#guard_msgs (drop info) in #check StrandMerkleRealization.ordinary_no_children
#guard_msgs (drop info) in #check StrandMerkleRealization.receiving_claims_empty
#guard_msgs (drop info) in #check MerkleWireCodec.nodeChildren_of_decoded

end LfzkV2.Current.Tests.StrandMerkleReceiving
