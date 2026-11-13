import LfzkV2.Current.Protocol.Setup
import LfzkV2.Current.ProofBodyBounds
import LfzkV2.Current.StatementCompiler
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
  /-- The global absorption invariant: only the statement, setup constants,
  prover messages and fixed labels are absorbed. -/
  setupOnly : CanonicalRequest.SetupOnly protocol.shape protocol.binary.nPublic protocol.metadata
  bindSalt : ∀ (key : FingerprintPrefix.Key protocol.binary.nPublic) (column : Fin c.n) (nonce : MerkleNonce),
    protocol.cfg.bindSalt key column nonce = (column,nonce)

namespace Setup
variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
  [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] {shared maskBits adviceBits : ℕ}

theorem independent (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits)
    (adviceBits := adviceBits)) :
    CanonicalRequest.ChallengeIndependent S.protocol.shape S.protocol.binary.nPublic S.protocol.metadata :=
  S.setupOnly.challengeIndependent

end Setup
end LfzkV2.Current.Soundness
