import LfzkV2.Current.CanonicalRate7
import LfzkV2.Current.IdealRuntime

/-! The concrete finite ideal-sampler model for the current rate-1/7
runtime. One oracle answer contains an independent link and joint challenge
block. Every challenge reader and uniformity law is constructed from that
block; no sampler-law or execution certificate is a theorem premise.
Actual SHAKE byte streams and rejection coupling are outside this model. -/
noncomputable section
namespace LfzkV2.Current.IdealRate7
open Application ApplicationSetup Finset
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

attribute [local instance] Classical.propDecidable

variable {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits calls tA Q TM : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B FixedRate.Rate7.certificate.k FixedRate.Rate7.certificate.s
  FixedRate.Rate7.certificate.n FixedRate.Rate7.certificate.t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) FixedRate.Rate7.certificate.k
  FixedRate.Rate7.certificate.s FixedRate.Rate7.certificate.n FixedRate.Rate7.certificate.t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)

abbrev Answer := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity

instance answerFintype : Fintype (Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) := by
  dsimp only [Answer, IdealRuntime.Answer, IdealSamples.Answer]
  infer_instance

private def openingIndices : Fin 84 ↪ Fin 2443 where
  toFun i := ⟨i.val,by have := i.isLt; omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun i : Fin 2443 => i.val) h)

instance answerNonempty : Nonempty (Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) :=
  ⟨fun component => match component with
    | .binary => fun _ => 0
    | .binaryNonzero => ⟨1,one_ne_zero⟩
    | .prime => fun _ => 0
    | .primeNonzero => (⟨1,one_ne_zero⟩,⟨1,one_ne_zero⟩)
    | .fingerprints => ((fun _ => 0,fun _ => 0),(fun _ => 0,fun _ => 0))
    | .batching => (fun _ => 0,fun _ => 0)
    | .opening => openingIndices⟩

variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  (Salt := MerkleWireCodec.Salt 2443))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  shape binary.nPublic)

/-- Sampling callbacks supplied in the arithmetic setup are overwritten
by the concrete common-answer projections. -/
abbrev challengeSetup := IdealRuntime.challengePublic binary prime P R
  countBinary countPrime binaryCapacity primeCapacity cfg

abbrev canonicalPublic := CanonicalRate7.wirePublic binary prime P R repr shape setup
  (challengeSetup binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)

abbrev draw := IdealRuntime.draw binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg

variable (fits : g.roles.length < 2^64)
variable (body : TwoOracleTree Bytes Digest Bytes
  (Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  (CanonicalRuntime.Output (Advice := Advice) binary shape) tA calls)
variable (dflt : Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)

/-- The actual early-selection source has the very same fingerprint
projection. This identity is derived, rather than provided by the caller. -/
def sampling
    (binaryFits : binary.degree ≤ binaryCapacity)
    (primeFits : prime.circuit.layers+1 ≤ primeCapacity)
    (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound) :
    RuntimeCover.SamplerLaws binary prime P R
      (canonicalPublic binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
      (CanonicalRate7.source binary prime P R repr shape setup
        (challengeSetup binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
        binaryCount metadata fits body dflt layout (TM := TM) (fun _ => dflt)) :=
  IdealRuntime.samplerLaws binary prime P R countBinary countPrime binaryCapacity primeCapacity
    (CanonicalRate7.wirePublic binary prime P R repr shape setup cfg)
    (CanonicalRate7.source binary prime P R repr shape setup
      (challengeSetup binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
      binaryCount metadata fits body dflt layout (TM := TM) (fun _ => dflt))
    rfl binaryFits primeFits bitsFit

abbrev rawEvent := CanonicalRate7.rawEvent (TM := TM) binary prime P R repr shape setup
  (challengeSetup binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
  binaryCount primeCount metadata fits body dflt
  (draw binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)

variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (binaryFits : binary.degree ≤ binaryCapacity)
variable (primeFits : prime.circuit.layers+1 ≤ primeCapacity)
variable (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound)
variable (primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (primePlanFits : primePlan.capacity ≤ primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)
variable (binaryPlanFits : binaryTemplate.capacity ≤ binaryCapacity)

include hlayout bodyFits binaryFits primeFits bitsFit primePlan primeGeometry primePlanFits
  binaryTemplate binaryGeometry binaryPlanFits in
/-- Accepted extraction failure for adaptive requests, actual canonical
query bytes, one shared Merkle tree, and the explicit finite ideal sampler.
Q counts original distinct transcript queries; replay appears only in the
digest-sized remainder. Repeated inputs return the same complete answer. -/
theorem ratio_le
    (hsupport : ∀ (mt : Fin TM → Digest)
      (Hraw : Bytes → Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity),
      (TranscriptV2.seen (fixLeft mt default body []) Hraw).card ≤ Q)
    (hspace : 4886+tA ≤ TM)
    (fallback : Bytes → Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) :
    ((univ.filter fun pair : (Fin TM → Digest) ×
        ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} →
          Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) =>
      rawEvent binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg
        binaryCount primeCount metadata fits body dflt pair.1
        (ByteOracleTransport.Codec.extendWindow
          (QueryRuntimeProbability.window repr shape setup binary.nPublic fits body) pair.2 fallback)).card : ℚ) /
      Fintype.card ((Fin TM → Digest) ×
        ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} →
          Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  let sample := sampling (TM := TM) binary prime P R countBinary countPrime binaryCapacity primeCapacity
    repr shape setup cfg binaryCount metadata fits body dflt layout binaryFits primeFits bitsFit
  have result := CanonicalRate7.ratio_le binary prime P R repr shape setup
    (challengeSetup binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
    binaryCount primeCount metadata fits body dflt
    (draw binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg)
    layout hlayout sample primePlan primeGeometry primePlanFits binaryTemplate binaryGeometry binaryPlanFits
    bodyFits
    (IdealRuntime.rawSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)
    rfl (IdealRuntime.querySampler binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    rfl hsupport hspace fallback
  exact result

end LfzkV2.Current.IdealRate7
