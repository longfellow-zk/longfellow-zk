import LfzkV2.Current.Protocol.Setup
import LfzkV2.Current.StrandMerkleMissingQueries

/-! Structural inputs needed for extraction soundness, kept separate from
the shared executable protocol model and the ZK sampler interface. -/
namespace LfzkV2.Current.Soundness

structure Inputs {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
    [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    {shared maskBits adviceBits : ℕ}
    (protocol : Protocol.Setup c g fields Advice B
      (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits)) where
  layout : StatementCompiler.Addresses protocol.P protocol.R
    protocol.binary.cells protocol.prime.remaining protocol.prime.pads
  bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound
  layoutCorrect : StatementCompiler.addresses protocol.P protocol.R
    protocol.binary.cells protocol.prime.remaining protocol.prime.pads = some layout
  bodyFits : ProofBodyBounds.bodyBound protocol.repr g ≤ CanonicalPrefix.maxLength

structure Setup (c : CertifiedProfile) (g : Geometry) (fields : Fields) (Advice B : Type)
    [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    {shared maskBits adviceBits : ℕ} where
  protocol : Protocol.Setup c g fields Advice B
    (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits)
  inputs : Inputs protocol
  fits : g.roles.length < 2^64
  fallbackPath : StrandMerkleMissingQueries.SelectedPath (n := c.n) (Salt := Fin c.n × MerkleNonce)
    («M» := (Joint.Pair.family protocol.First protocol.Second).Leaf) (D := Digest) (Enc := Bytes)
  independent : CanonicalRequest.ChallengeIndependent protocol.shape protocol.binary.nPublic protocol.metadata
  bindSalt : ∀ (key : FingerprintPrefix.Key protocol.binary.nPublic) (column : Fin c.n) (nonce : MerkleNonce),
    protocol.cfg.bindSalt key column nonce = (column,nonce)

end LfzkV2.Current.Soundness
