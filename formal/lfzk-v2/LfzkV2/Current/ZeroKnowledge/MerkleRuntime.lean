import LfzkV2.Current.MerkleWireCodec

/-! The masking argument uses a pair of affine-backend leaves. The runtime
uses the same leaves inside the existing typed two-participant tuple. This
transport changes neither row order nor any encoded hash input. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleRuntime
open Merkle Merkle.MH RecursivePolygero

/-- A linear backend leaf is a finite vector over its field. Its finite
representation depends only on the row count, not on a verifier or transcript
configuration. Keep this instance local at callers to avoid competing with
their existing representations of the same finite type. -/
abbrev leafFintype (F : Type) [Fintype F] (rows : ℕ) : Fintype (MerkleCompiler.Leaf F rows 0) :=
  Fintype.ofEquiv _ (OpeningBody.leafEquiv F rows)

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)

def participantLeaf : MerkleCompiler.Leaf P.Carrier P.backend.nw 0 ≃ P.Leaf :=
  Equiv.cast (by change MerkleCompiler.Leaf P.Carrier P.backend.nw 0 =
    MerkleCompiler.Leaf P.Carrier P.backend.nw P.backend.nq; rw [P.linearOnly])

def tupleLeaf :
    (MerkleCompiler.Leaf P.Carrier P.backend.nw 0 × MerkleCompiler.Leaf R.Carrier R.backend.nw 0) ≃
      (Joint.Pair.family P R).Leaf :=
  ((participantLeaf P).prodCongr (participantLeaf R)).trans (MerkleWireCodec.tupleLeafEquiv P R)

variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (fits : n ≤ 2^64)

/-- Pull back the actual runtime byte codec to the pair used by the backend
coupling. The public index and 32-byte nonce retain their literal encoding. -/
def codec : Codec (MerkleWireCodec.Salt n)
    (MerkleCompiler.Leaf P.Carrier P.backend.nw 0 × MerkleCompiler.Leaf R.Carrier R.backend.nw 0)
    Digest Bytes where
  leafEnc value := (MerkleWireCodec.codec P R repr binary prime context fits).leafEnc
    (value.1,tupleLeaf P R value.2)
  nodeEnc := (MerkleWireCodec.codec P R repr binary prime context fits).nodeEnc

theorem codec_inj : (codec P R repr binary prime context fits).Inj := by
  constructor
  · intro a b equal
    rcases a with ⟨saltA,leafA⟩
    rcases b with ⟨saltB,leafB⟩
    have decoded := (MerkleWireCodec.codec_inj P R repr binary prime context fits).leaf equal
    have salt : saltA = saltB := congrArg Prod.fst decoded
    have leaves : leafA = leafB := (tupleLeaf P R).injective (congrArg Prod.snd decoded)
    cases salt
    cases leaves
    rfl
  · exact (MerkleWireCodec.codec_inj P R repr binary prime context fits).node

@[simp] theorem leaf_bytes (column : Fin n) (nonce : Digest)
    (leaf : MerkleCompiler.Leaf P.Carrier P.backend.nw 0 × MerkleCompiler.Leaf R.Carrier R.backend.nw 0) :
    (codec P R repr binary prime context fits).leafEnc ((column,nonce),leaf) =
      (MerkleWireCodec.codec P R repr binary prime context fits).leafEnc
        ((column,nonce),tupleLeaf P R leaf) := rfl

@[simp] theorem node_bytes (children : Digest × Digest) :
    (codec P R repr binary prime context fits).nodeEnc children =
      (MerkleWireCodec.codec P R repr binary prime context fits).nodeEnc children := rfl

/-- The transport is exactly the physical `u,m,witness,fstar` map already
used to encode and decode the proof's opened rows. -/
theorem physicalLeaf
    (binaryRows : Fin (P.backend.nw+3) → P.Carrier)
    (primeRows : Fin (R.backend.nw+3) → R.Carrier) :
    tupleLeaf P R (OpeningBody.leafEquiv P.Carrier P.backend.nw binaryRows,
      OpeningBody.leafEquiv R.Carrier R.backend.nw primeRows) =
      MerkleWireCodec.physicalLeafEquiv P R (binaryRows,primeRows) := rfl

end LfzkV2.Current.ZeroKnowledge.MerkleRuntime
