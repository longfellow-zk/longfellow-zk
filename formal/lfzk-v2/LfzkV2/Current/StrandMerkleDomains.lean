import LfzkV2.Current.MerkleWireCodec
import TranscriptV2.StrandEncoding

/-! Separation of the actual SHA-256 byte domains. Merkle inputs start
with ASCII `p`; numbered strand nodes and PRF inputs start with 1 and 0.
This is a syntax fact and does not require collision resistance. -/
namespace LfzkV2.Current.StrandMerkleDomains
open TranscriptV2

private theorem input_ne_merkleHead (input : Strand.Input) (raw : Bytes)
    (head : raw.head? = some (112 : Framing.Byte)) : input.encode ≠ raw := by
  intro same
  have first := (congrArg List.head? same).trans head
  cases input with
  | prf id parent counter =>
      change some (0 : Framing.Byte) = some (112 : Framing.Byte) at first
      exact (by decide : (0 : Framing.Byte) ≠ 112) (Option.some.inj first)
  | root message =>
      change some (1 : Framing.Byte) = some (112 : Framing.Byte) at first
      exact (by decide : (1 : Framing.Byte) ≠ 112) (Option.some.inj first)
  | node id parents message =>
      change some (1 : Framing.Byte) = some (112 : Framing.Byte) at first
      exact (by decide : (1 : Framing.Byte) ≠ 112) (Option.some.inj first)

/-- Ordinary transcript inputs cannot also supply Merkle child targets. -/
theorem nodeChildren_input (input : Strand.Input) :
    MerkleWireCodec.nodeChildren input.encode = none := by
  unfold MerkleWireCodec.nodeChildren
  apply if_neg
  cases input with
  | prf id parent counter =>
      change some (0 : Framing.Byte) ≠ some 112
      decide
  | root message =>
      change some (1 : Framing.Byte) ≠ some 112
      decide
  | node id parents message =>
      change some (1 : Framing.Byte) ≠ some 112
      decide

variable {k s n t : ℕ} {fields : Fields} {Advice : Type}
variable (P R : Joint.Participant k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

local notation "codec" => MerkleWireCodec.codec P R repr binary prime context columnsFit

theorem input_ne_leaf (input : Strand.Input)
    (value : MerkleWireCodec.Salt n × (Joint.Pair.family P R).Leaf) :
    input.encode ≠ (codec).leafEnc value := by
  apply input_ne_merkleHead
  rw [MerkleWireCodec.leaf_encode]
  rfl

theorem input_ne_node (input : Strand.Input) (index : ℕ) (children : Digest × Digest) :
    input.encode ≠ (codec).nodeEnc index children := by
  apply input_ne_merkleHead
  rw [MerkleWireCodec.node_encode]
  rfl

end LfzkV2.Current.StrandMerkleDomains
