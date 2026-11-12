import LfzkV2.Current.MerkleWireCodec

/-! The earlier whole-answer proofs use the original Merkle node syntax,
which predates heap-index binding. Keep that historical model explicit so
its reusable masking and simulation proofs cannot silently describe the
current indexed verifier. Leaf encoding and physical row maps are shared. -/
noncomputable section
namespace LfzkV2.Current.WholeAnswerMerkle
open Merkle Merkle.MH
open scoped Classical

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

def node (context : Digest) : PrefixCodec (Digest × Digest) :=
  (ProofBodyCodec.digest.pair ProofBodyCodec.digest).prefixed
    (MerkleWireCodec.nodeDomain ++ List.ofFn context)

def codec : Codec (MerkleWireCodec.Salt n) (Joint.Pair.family P R).Leaf Digest Bytes where
  leafEnc := (MerkleWireCodec.leaf P R repr binary prime context columnsFit).encode
  nodeEnc := (node context).encode

def decoders : RoleDecoders (codec P R repr binary prime context columnsFit) where
  leafDec := CanonicalPrefix.readWhole (MerkleWireCodec.leaf P R repr binary prime context columnsFit)
  nodeDec := CanonicalPrefix.readWhole (node context)
  leaf_roundTrip := CanonicalPrefix.readWhole_encode _
  node_roundTrip := CanonicalPrefix.readWhole_encode _
  leaf_sound bytes value h := (CanonicalPrefix.readWhole_canonical _ bytes value h).symm
  node_sound bytes value h := (CanonicalPrefix.readWhole_canonical _ bytes value h).symm

theorem codec_inj : (codec P R repr binary prime context columnsFit).Inj :=
  (decoders P R repr binary prime context columnsFit).inj

theorem node_encode (value : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).nodeEnc value =
      MerkleWireCodec.nodeDomain ++ List.ofFn context ++ List.ofFn value.1 ++ List.ofFn value.2 := by
  simp only [codec,node,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,ProofBodyCodec.digest,PrefixCodec.bytes_encode,List.append_assoc]

theorem node_prefix (value : Digest × Digest) :
    MerkleWireCodec.nodeDomain <+: (codec P R repr binary prime context columnsFit).nodeEnc value := by
  rw [node_encode]
  exact ⟨List.ofFn context ++ List.ofFn value.1 ++ List.ofFn value.2,
    by simp only [List.append_assoc]⟩

end LfzkV2.Current.WholeAnswerMerkle
