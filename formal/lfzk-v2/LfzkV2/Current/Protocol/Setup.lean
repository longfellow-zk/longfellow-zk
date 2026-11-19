import LfzkV2.Current.CanonicalRuntime
import LfzkV2.Current.CertifiedProfile
import LfzkV2.Current.FrontendSchedule
import LfzkV2.Current.IdealRuntime
import LfzkV2.Current.MerkleWireCodec

/-! Public protocol data and structural consistency. This record contains
no execution, failure-cover or probabilistic soundness hypotheses. -/
namespace LfzkV2.Current.Protocol
open Application ApplicationSetup TranscriptV2

structure Setup (c : CertifiedProfile) (g : Geometry) (fields : Fields) (Advice B : Type)
    [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    {shared maskBits adviceBits : ℕ} where
  binary : BinaryPublic B shared maskBits adviceBits
  prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared
  P : FieldBackend B c.k c.s c.n c.t
  R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) c.k c.s c.n c.t
  countBinary : ℕ
  countPrime : ℕ
  binaryCapacity : ℕ
  primeCapacity : ℕ
  /-- The transcript format. -/
  fmt : Format g fields Advice binary.nPublic
  binaryPlan : FrontendSchedule.Plan B binary.circuit
  primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit
  binaryGeometry : binaryPlan.frontend = g.binary
  primeGeometry : primePlan.frontend = g.prime
  binaryFits : binaryPlan.capacity ≤ binaryCapacity
  primeFits : primePlan.capacity ≤ primeCapacity
  degreeFits : binary.degree ≤ binaryCapacity
  rowsFit : prime.circuit.layers+1 ≤ primeCapacity
  cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
    (Base := fmt.Base)
    (Key := fmt.Key)
    (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (Salt := Fin c.n × MerkleNonce)
  binaryCount : fmt.binaryPublic = binary.nPublic
  primeCount : fmt.primePublic = prime.nPublic
  metadata : fmt.RequestMetadata
    (IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  columnsFit : c.n ≤ 2^64

namespace Setup
variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (S : Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))

abbrev Answer := IdealRuntime.Answer S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity
abbrev Point := S.fmt.Point
abbrev Value := S.fmt.Value
abbrev Output := CanonicalRuntime.FormatOutput S.binary S.fmt

noncomputable abbrev ideal := IdealRuntime.challengePublic S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity S.cfg

noncomputable abbrev wire := CanonicalRuntime.wirePublic S.binary S.prime S.P S.R
  S.fmt S.ideal

noncomputable abbrev earlier := CanonicalRuntime.earlier S.binary S.prime S.P S.R
  S.fmt S.ideal S.binaryCount S.metadata

noncomputable abbrev chain := RuntimeAdaptiveVerifier.chain S.binary S.prime S.P S.R S.wire S.earlier
abbrev bodyCodec := S.fmt.body
abbrev hashPublic := S.fmt.hashPublic
abbrev context := S.fmt.key
noncomputable abbrev primePublic := CanonicalRuntime.decodePrimePublic S.binary S.prime S.P S.R
  S.fmt S.ideal S.primeCount
noncomputable abbrev draw := IdealRuntime.draw S.binary S.prime S.P S.R
  S.countBinary S.countPrime S.binaryCapacity S.primeCapacity S.cfg
abbrev First := (S.P.indexed S.countBinary).participant
abbrev Second := (S.R.indexed S.countPrime).participant
abbrev merkleCodec := MerkleWireCodec.codec S.First S.Second S.fmt.scalars
  S.cfg.binaryField S.cfg.primeField S.fmt.jointContext S.columnsFit
abbrev merkleDecoders := MerkleWireCodec.decoders S.First S.Second S.fmt.scalars
  S.cfg.binaryField S.cfg.primeField S.fmt.jointContext S.columnsFit

end Setup
end LfzkV2.Current.Protocol
