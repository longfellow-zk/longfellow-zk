import LfzkV2.Current.IdealRate7
import LfzkV2.Current.ProofOutput

/-! Arbitrary serialized proof outputs in the finite ideal-sampler model.
The actual complete-proof parser rejects malformed or trailing bytes before
verification. Normalizing a successful parse changes no adversary query,
and its fallback value is irrelevant whenever the output is rejected. -/
noncomputable section
namespace LfzkV2.Current.IdealProofRate7
open Application ApplicationSetup Finset
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
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
variable (fits : g.roles.length < 2^64)

abbrev RawOutput := CanonicalRuntime.Request binary shape × Bytes

variable (body : TwoOracleTree Bytes Digest Bytes
  (Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  (RawOutput binary shape) tA calls)
variable (fallbackProof : Proof g fields Advice (OpeningBody.Authentication g))
variable (dflt : Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)

def normalizedBody := ProofOutput.normalize repr fallbackProof body

/-- Parsing is a verifier operation in the event itself, not a hypothesis
that an adversary's serialized output is well formed. -/
def rawEvent (mt : Fin TM → Digest)
    (Hraw : Bytes → Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) : Prop :=
  (ProofOutput.read (g := g) repr (((fixLeft mt default body []).run Hraw).1.2)).isSome ∧
    IdealRate7.rawEvent binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg
      binaryCount primeCount metadata fits
      (normalizedBody binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape body fallbackProof)
      dflt mt Hraw

omit [Fintype B] [DecidableEq B] [∀ side, Fintype (fields side)] [Fintype Advice] in
/-- On an accepted parse the normalizer uses exactly those decoded proof
bytes, including the final seal. No proof/body correspondence is supplied. -/
theorem output_of_parse (mt : Fin TM → Digest)
    (Hraw : Bytes → Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (proof : Proof g fields Advice (OpeningBody.Authentication g))
    (hparse : ProofOutput.read repr (((fixLeft mt default body []).run Hraw).1.2) = some proof) :
    ((fixLeft mt default
      (normalizedBody binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape body fallbackProof) []).run Hraw).1 =
      ⟨((fixLeft mt default body []).run Hraw).1.1,proof⟩ := by
  rw [normalizedBody,ProofOutput.normalize,ProofOutput.run_map]
  exact ProofOutput.decode_of_read repr fallbackProof _ proof hparse

variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
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
/-- Complete accepted-extraction-failure bound for arbitrary proof bytes,
adaptive requests, actual transcript/Merkle input encodings, and the explicit
finite ideal joint sampler. Q counts the original program's distinct byte
queries. Malformed proof output is rejected, with no correctness premise. -/
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
        binaryCount primeCount metadata fits body fallbackProof dflt pair.1
        (ByteOracleTransport.Codec.extendWindow
          (QueryRuntimeProbability.window repr shape setup binary.nPublic fits body) pair.2 fallback)).card : ℚ) /
      Fintype.card ((Fin TM → Digest) ×
        ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} →
          Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+tA*(tA-1)/2+(4886+tA)*(2*tA+g.roles.length+Q+2) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  have result := IdealRate7.ratio_le binary prime P R countBinary countPrime binaryCapacity primeCapacity
    repr shape setup cfg binaryCount primeCount metadata fits
    (normalizedBody binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape body fallbackProof)
    dflt layout hlayout bodyFits binaryFits primeFits bitsFit primePlan primeGeometry primePlanFits
    binaryTemplate binaryGeometry binaryPlanFits
    (by
      intro mt H
      rw [normalizedBody,ProofOutput.normalize,ProofOutput.seen_map]
      exact hsupport mt H) hspace fallback
  have hwindow : QueryRuntimeProbability.window repr shape setup binary.nPublic fits
      (normalizedBody binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape body fallbackProof) =
      QueryRuntimeProbability.window repr shape setup binary.nPublic fits body :=
    ProofOutput.window_map (QueryRuntime.Runtime.codec repr shape setup binary.nPublic fits)
      (ProofOutput.decode repr fallbackProof) body
  rw [hwindow] at result
  let Experiment := (Fin TM → Digest) ×
    ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} →
      Digest × IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  have hsubset :
      (univ.filter fun pair : Experiment => rawEvent binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup cfg
        binaryCount primeCount metadata fits body fallbackProof dflt pair.1
        (ByteOracleTransport.Codec.extendWindow
          (QueryRuntimeProbability.window repr shape setup binary.nPublic fits body) pair.2 fallback)) ⊆
      (univ.filter fun pair : Experiment => IdealRate7.rawEvent binary prime P R countBinary countPrime binaryCapacity primeCapacity
        repr shape setup cfg binaryCount primeCount metadata fits
        (normalizedBody binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape body fallbackProof)
        dflt pair.1 (ByteOracleTransport.Codec.extendWindow
          (QueryRuntimeProbability.window repr shape setup binary.nPublic fits body) pair.2 fallback)) := by
    intro pair hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hp).2.2⟩
  have correction : 4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) =
      4*Q+1+tA*(tA-1)/2+(4886+tA)*(2*tA+g.roles.length+Q+2) := by
    unfold Bcs.AdaptiveCommit.adaptiveNumerator
    ring
  simpa only [correction] using
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card hsubset)) (Nat.cast_nonneg _)).trans result

end LfzkV2.Current.IdealProofRate7
