import LfzkV2.Current.Protocol.Setup
import TranscriptV2.StrandEncoding

/-! Executable sampling data, without role-factor constructions or balance
laws. Privacy and honest execution need only this interface. -/
namespace LfzkV2.Current.Protocol
open Merkle.RandomOracle TranscriptV2

/-- A physical sampler may fail. This record assumes neither balanced
fibers nor successful sampling. -/
structure ExecutionSampler
    {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
    [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    {shared maskBits adviceBits : ℕ}
    (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
    (blocks : ℕ) where
  sample : S.Point → Tree Strand.Word Digest (Option S.Answer) blocks

end LfzkV2.Current.Protocol
