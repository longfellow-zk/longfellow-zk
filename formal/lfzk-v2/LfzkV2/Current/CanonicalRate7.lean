import LfzkV2.Current.CanonicalOracle
import LfzkV2.Current.QueryRuntimeProbability
import LfzkV2.Current.RuntimeAdaptiveRate7
import LfzkV2.Current.MerkleWireCodec
import LfzkV2.Current.CanonicalVerifierAgreement

/-! The rate-1/7 runtime on canonical transcript and Merkle byte inputs.
Public requests remain adaptive. Invalid transcript bytes are independent
auxiliary oracle coordinates; their calls remain in the raw query budget. -/
noncomputable section
namespace LfzkV2.Current.CanonicalRate7
open Application ApplicationSetup Finset
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

attribute [local instance] Classical.propDecidable

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable {shared maskBits adviceBits calls tA Q TM : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B FixedRate.Rate7.certificate.k FixedRate.Rate7.certificate.s FixedRate.Rate7.certificate.n FixedRate.Rate7.certificate.t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) FixedRate.Rate7.certificate.k FixedRate.Rate7.certificate.s FixedRate.Rate7.certificate.n FixedRate.Rate7.certificate.t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := MerkleWireCodec.Salt 2443))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)

abbrev Point := QueryRuntime.Runtime.Point repr shape setup binary.nPublic
abbrev Output := CanonicalRuntime.Output (Advice := Advice) binary shape

/-- Column and nonce are the actual salt. No salt-encoding callback is
left for an application to replace. -/
def basePublic : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
    (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := MerkleWireCodec.Salt 2443) :=
  { cfg with bindSalt := MerkleWireCodec.bindSalt }

abbrev wirePublic := CanonicalRuntime.wirePublic binary prime P R repr shape setup
  (basePublic binary prime P R repr shape setup cfg)

abbrev earlier := CanonicalRuntime.earlier binary prime P R repr shape setup
  (basePublic binary prime P R repr shape setup cfg) binaryCount metadata

abbrev decodePublic := CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
  (basePublic binary prime P R repr shape setup cfg) primeCount

def merkleCodec := MerkleWireCodec.codec
  (RuntimeVerifier.first binary prime P R (wirePublic binary prime P R repr shape setup cfg)).participant
  (RuntimeVerifier.second binary prime P R (wirePublic binary prime P R repr shape setup cfg)).participant
  repr cfg.binaryField cfg.primeField setup.jointContext (by decide)

def merkleDecoders := MerkleWireCodec.decoders
  (RuntimeVerifier.first binary prime P R (wirePublic binary prime P R repr shape setup cfg)).participant
  (RuntimeVerifier.second binary prime P R (wirePublic binary prime P R repr shape setup cfg)).participant
  repr cfg.binaryField cfg.primeField setup.jointContext (by decide)

instance leafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)).Leaf :=
  ⟨MerkleWireCodec.physicalLeafEquiv _ _ (fun _ => 0,fun _ => 0)⟩

local instance saltInhabited : Inhabited (MerkleWireCodec.Salt FixedRate.Rate7.certificate.n) :=
  (inferInstance : Inhabited (MerkleWireCodec.Salt 2443))

variable (fits : g.roles.length < 2^64)

def byteCodec := QueryRuntime.Runtime.codec repr shape setup binary.nPublic fits

variable (body : TwoOracleTree Bytes Digest Bytes (Digest × C) (Output (Advice := Advice) binary shape) tA calls)
variable (dflt : Digest × C)

def typedBody (outside : Bytes → Digest × C) :=
  (byteCodec binary repr shape setup fits).program outside body

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R (wirePublic binary prime P R repr shape setup cfg))
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)

def source (outside : Bytes → Digest × C) :=
  letI := leafInhabited binary prime P R repr shape setup cfg
  RuntimeAdaptiveRate7.source binary prime P R (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)
    (merkleCodec binary prime P R repr shape setup cfg) (merkleDecoders binary prime P R repr shape setup cfg)
    dflt (typedBody binary repr shape setup fits body outside) layout (fun _ : Fin TM => 0)

variable (samplers : RuntimeCover.SamplerLaws binary prime P R (wirePublic binary prime P R repr shape setup cfg)
  (source binary prime P R repr shape setup cfg binaryCount metadata fits body dflt layout (TM := TM) (fun _ => dflt)))
variable (primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (primeFits : primePlan.capacity ≤ samplers.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)
variable (binaryFits : binaryTemplate.capacity ≤ samplers.binaryCapacity)

def samplingAt (outside : Bytes → Digest × C) : RuntimeCover.SamplerLaws binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (source binary prime P R repr shape setup cfg binaryCount metadata fits body dflt layout (TM := TM) outside) :=
  samplers.retarget _ (by rfl)

def accepted (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H : Point binary repr shape setup → Digest × C) : Prop :=
  letI := leafInhabited binary prime P R repr shape setup cfg
  RuntimeAdaptiveCommitment.Accepted FixedRate.Rate7.certificate binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)
    (CanonicalRequest.hashPublic binary.nPublic)
    (decodePublic binary prime P R repr shape setup cfg primeCount) draw
    (merkleCodec binary prime P R repr shape setup cfg) dflt
    (typedBody binary repr shape setup fits body outside) mt H

def extractionFailure (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H : Point binary repr shape setup → Digest × C) : Prop :=
  letI := leafInhabited binary prime P R repr shape setup cfg
  RuntimeAdaptiveCommitment.ExtractionFailure FixedRate.Rate7.certificate binary prime P R
    (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)
    (CanonicalRequest.hashPublic binary.nPublic)
    (decodePublic binary prime P R repr shape setup cfg primeCount) draw
    (merkleCodec binary prime P R repr shape setup cfg) (merkleDecoders binary prime P R repr shape setup cfg)
    dflt (typedBody binary repr shape setup fits body outside) mt H

def commitmentSetup (outside : Bytes → Digest × C) :=
  letI := leafInhabited binary prime P R repr shape setup cfg
  RuntimeAdaptiveMerkle.setup binary prime P R (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata) dflt
    (typedBody binary repr shape setup fits body outside)

variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)

section Agreement
include bodyFits

omit [Fintype C] [Nonempty C] [DecidableEq C] in
theorem atOracle_eq (outside : Bytes → Digest × C)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    (commitmentSetup binary prime P R repr shape setup cfg binaryCount metadata fits body dflt outside).atOracle H =
      (commitmentSetup binary prime P R repr shape setup cfg binaryCount metadata fits body dflt outside).atOracle H' := by
  apply CanonicalOracle.atOracle_eq
  change Bcs.TotalOracleCommit.answerRight H
      (((byteCodec binary repr shape setup fits).program outside body).bindRight
        (RuntimeAdaptiveVerifier.chain binary prime P R (wirePublic binary prime P R repr shape setup cfg)
          (earlier binary prime P R repr shape setup cfg binaryCount metadata)).recompute) = _
  exact CanonicalOracle.answered_program_recompute _ _ outside H H' agree
    (fun output oracle index hi => CanonicalVerifierAgreement.point_canonical binary prime P R repr shape setup
      (basePublic binary prime P R repr shape setup cfg) binaryCount metadata bodyFits output oracle index hi.le) body

omit bodyFits [Fintype B] [DecidableEq B] [Fintype C] [Nonempty C] [DecidableEq C] in
theorem originalOutput_eq (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    RuntimeAdaptiveMerkle.originalOutput (typedBody binary repr shape setup fits body outside) mt H =
      RuntimeAdaptiveMerkle.originalOutput (typedBody binary repr shape setup fits body outside) mt H' :=
  congrArg Prod.fst (CanonicalOracle.program_run_eq (byteCodec binary repr shape setup fits) outside H H' agree body mt default [])

omit [Fintype C] [Nonempty C] [DecidableEq C] in
theorem merkleOracle_eq (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    RuntimeAdaptiveMerkle.merkleOracle binary prime P R (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (merkleCodec binary prime P R repr shape setup cfg) dflt
      (typedBody binary repr shape setup fits body outside) mt H =
    RuntimeAdaptiveMerkle.merkleOracle binary prime P R (wirePublic binary prime P R repr shape setup cfg)
      (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (merkleCodec binary prime P R repr shape setup cfg) dflt
      (typedBody binary repr shape setup fits body outside) mt H' := by
  change ((commitmentSetup binary prime P R repr shape setup cfg binaryCount metadata fits body dflt outside).atOracle H).merkleOracle _ mt _ = _
  rw [atOracle_eq binary prime P R repr shape setup cfg binaryCount metadata fits body dflt bodyFits outside H H' agree]
  rfl

omit [Fintype C] [Nonempty C] [DecidableEq C] in
theorem cutOracle_eq (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    RuntimeAdaptiveCommitment.cutOracle FixedRate.Rate7.certificate binary prime P R
      (wirePublic binary prime P R repr shape setup cfg) (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (merkleCodec binary prime P R repr shape setup cfg) (merkleDecoders binary prime P R repr shape setup cfg)
      dflt (typedBody binary repr shape setup fits body outside) mt H =
    RuntimeAdaptiveCommitment.cutOracle FixedRate.Rate7.certificate binary prime P R
      (wirePublic binary prime P R repr shape setup cfg) (earlier binary prime P R repr shape setup cfg binaryCount metadata)
      (merkleCodec binary prime P R repr shape setup cfg) (merkleDecoders binary prime P R repr shape setup cfg)
      dflt (typedBody binary repr shape setup fits body outside) mt H' := by
  letI := leafInhabited binary prime P R repr shape setup cfg
  funext key
  have hc :
      ((commitmentSetup binary prime P R repr shape setup cfg binaryCount metadata fits body dflt outside).atOracle H).ctxAt
        mt Bcs.TotalOracleCommit.Setup.emptyTape key =
      ((commitmentSetup binary prime P R repr shape setup cfg binaryCount metadata fits body dflt outside).atOracle H').ctxAt
        mt Bcs.TotalOracleCommit.Setup.emptyTape key :=
    congrArg (fun experiment => experiment.ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape key)
      (atOracle_eq binary prime P R repr shape setup cfg binaryCount metadata fits body dflt bodyFits outside H H' agree)
  exact congrArg (fun context : FingerprintPrefix.Key binary.nPublic × List (Bytes × Digest) =>
    Joint.Pair.oracleEquiv _ _
      ((RuntimeVerifier.Family binary prime P R (wirePublic binary prime P R repr shape setup cfg)).extractedOracle
        (merkleDecoders binary prime P R repr shape setup cfg)
        ((wirePublic binary prime P R repr shape setup cfg).root context.1) context.2)) hc

omit [Fintype C] [Nonempty C] [DecidableEq C] in
theorem accepted_iff (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H ↔
      accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H' := by
  letI : Inhabited (RuntimeVerifier.Family binary prime P R
      (CanonicalRuntime.wirePublic binary prime P R repr shape setup
        (basePublic binary prime P R repr shape setup cfg))).Leaf :=
    leafInhabited binary prime P R repr shape setup cfg
  unfold accepted RuntimeAdaptiveCommitment.Accepted
  rw [originalOutput_eq binary repr shape setup fits body outside mt H H' agree,
    merkleOracle_eq binary prime P R repr shape setup cfg binaryCount metadata fits body dflt bodyFits outside mt H H' agree]
  simp only [wirePublic,earlier,decodePublic]
  rw [RuntimeAdaptiveVerifier.verify_true_iff,RuntimeAdaptiveVerifier.verify_true_iff,
    CanonicalVerifierAgreement.decode_eq binary prime P R repr shape setup
      (basePublic binary prime P R repr shape setup cfg) binaryCount metadata bodyFits primeCount draw _ H H' agree]
  apply exists_congr
  intro decoded
  exact and_congr Iff.rfl (CanonicalVerifierAgreement.checks_iff binary prime P R repr shape setup
    (basePublic binary prime P R repr shape setup cfg) binaryCount metadata bodyFits
    (merkleCodec binary prime P R repr shape setup cfg) _ _ H H' agree decoded)

omit [Fintype C] [Nonempty C] [DecidableEq C] in
theorem extractionFailure_iff (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H H' : Point binary repr shape setup → Digest × C)
    (agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → H point = H' point) :
    extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H ↔
      extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H' := by
  letI : Inhabited (RuntimeVerifier.Family binary prime P R
      (CanonicalRuntime.wirePublic binary prime P R repr shape setup
        (basePublic binary prime P R repr shape setup cfg))).Leaf :=
    leafInhabited binary prime P R repr shape setup cfg
  unfold extractionFailure RuntimeAdaptiveCommitment.ExtractionFailure
  rw [originalOutput_eq binary repr shape setup fits body outside mt H H' agree]
  simp only [wirePublic,earlier,decodePublic]
  rw [CanonicalVerifierAgreement.decode_eq binary prime P R repr shape setup
      (basePublic binary prime P R repr shape setup cfg) binaryCount metadata bodyFits primeCount draw _ H H' agree]
  unfold RuntimeAdaptiveBackend.authentication
  have hc := cutOracle_eq binary prime P R repr shape setup cfg binaryCount metadata fits body dflt bodyFits outside mt H H' agree
  simp only [wirePublic,earlier] at hc
  rw [hc]

end Agreement

include hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits in
/-- Conditioning only the outside byte answers preserves the same
distinct-query bound. All profile and candidate-list costs are internal. -/
theorem typed_ratio_le (outside : Bytes → Digest × C)
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R (wirePublic binary prime P R repr shape setup cfg)))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet 2443 84))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R (wirePublic binary prime P R repr shape setup cfg))
    (hsupport : ∀ (mt : Fin TM → Digest) (Hraw : Bytes → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) Hraw).card ≤ Q)
    (hspace : 4886+tA ≤ TM) :
    ((univ.filter fun pair : (Fin TM → Digest) × (Point binary repr shape setup → Digest × C) =>
      accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside pair.1 pair.2 ∧
      extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside pair.1 pair.2).card : ℚ) /
        Fintype.card ((Fin TM → Digest) × (Point binary repr shape setup → Digest × C)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  letI := leafInhabited binary prime P R repr shape setup cfg
  have result := RuntimeAdaptiveRate7.ratio_le binary prime P R (wirePublic binary prime P R repr shape setup cfg)
    (earlier binary prime P R repr shape setup cfg binaryCount metadata)
    (CanonicalRequest.hashPublic binary.nPublic) (decodePublic binary prime P R repr shape setup cfg primeCount) draw
    (merkleCodec binary prime P R repr shape setup cfg) (merkleDecoders binary prime P R repr shape setup cfg)
    dflt (typedBody binary repr shape setup fits body outside) layout hlayout
    (samplingAt binary prime P R repr shape setup cfg binaryCount metadata fits body dflt layout samplers outside)
    primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits rawSampler hraw querySampler hquery
    (fun mt H => ((byteCodec binary repr shape setup fits).program_seen_card_le outside H mt default body []).trans
      (hsupport mt ((byteCodec binary repr shape setup fits).oracle outside H))) hspace
  simpa only [accepted,extractionFailure,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_pow] using result

def restricted (Hraw : Bytes → Digest × C) : Point binary repr shape setup → Digest × C :=
  (byteCodec binary repr shape setup fits).restrict Hraw (fun _ => dflt)

/-- Evaluate the original byte-query program and the canonical verifier
using the same byte oracle. The typed cache is reconstructed internally.
Only noncanonical logical aliases receive the unused fallback answer. -/
def rawEvent (mt : Fin TM → Digest) (Hraw : Bytes → Digest × C) : Prop :=
  accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw Hraw mt
      (restricted binary repr shape setup fits dflt Hraw) ∧
    extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw Hraw mt
      (restricted binary repr shape setup fits dflt Hraw)

omit [Fintype B] [DecidableEq B] [Fintype C] [Nonempty C] [DecidableEq C] in
/-- The simulator returns exactly the original raw program's output.
Outside-image byte calls are answered in place and retain their cost. -/
theorem raw_output (mt : Fin TM → Digest) (Hraw : Bytes → Digest × C) :
    RuntimeAdaptiveMerkle.originalOutput (typedBody binary repr shape setup fits body Hraw) mt
      (restricted binary repr shape setup fits dflt Hraw) = ((fixLeft mt default body []).run Hraw).1 := by
  change ((fixLeft mt default ((byteCodec binary repr shape setup fits).program Hraw body) []).run
    ((byteCodec binary repr shape setup fits).restrict Hraw (fun _ => dflt))).1 = _
  rw [ByteOracleTransport.Codec.fixLeft_program,ByteOracleTransport.Codec.run_tree,
    ByteOracleTransport.Codec.oracle_restrict]

include bodyFits in
omit [Fintype C] [Nonempty C] [DecidableEq C] in
/-- Removing unused malformed typed coordinates preserves actual
acceptance and the same first-context extractor, without a loss factor. -/
theorem raw_event_oracle (outside : Bytes → Digest × C) (mt : Fin TM → Digest)
    (H : Point binary repr shape setup → Digest × C) :
    rawEvent binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw mt
      ((byteCodec binary repr shape setup fits).oracle outside H) ↔
      accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H ∧
        extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt H := by
  let norm := restricted binary repr shape setup fits dflt ((byteCodec binary repr shape setup fits).oracle outside H)
  have agree : ∀ point, QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point → norm point = H point :=
    fun point hp => CanonicalOracle.restrict_oracle (byteCodec binary repr shape setup fits) outside H (fun _ => dflt) point hp
  have ha : accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw
      ((byteCodec binary repr shape setup fits).oracle outside H) mt norm ↔
      accepted binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt norm := by
    unfold accepted typedBody
    rw [CanonicalOracle.program_oracle]
  have hf : extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw
      ((byteCodec binary repr shape setup fits).oracle outside H) mt norm ↔
      extractionFailure binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw outside mt norm := by
    unfold extractionFailure typedBody
    rw [CanonicalOracle.program_oracle]
  exact (and_congr ha hf).trans (and_congr
    (accepted_iff binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw bodyFits outside mt norm H agree)
    (extractionFailure_iff binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw bodyFits outside mt norm H agree))

include bodyFits hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits in
/-- The actual raw event under a fixed outside-image oracle. Oracle
normalization preserves the selected extractor and introduces no factor. -/
theorem conditioned_ratio_le (outside : Bytes → Digest × C)
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R (wirePublic binary prime P R repr shape setup cfg)))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet 2443 84))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R (wirePublic binary prime P R repr shape setup cfg))
    (hsupport : ∀ (mt : Fin TM → Digest) (Hraw : Bytes → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) Hraw).card ≤ Q)
    (hspace : 4886+tA ≤ TM) :
    ((univ.filter fun pair : (Fin TM → Digest) × (Point binary repr shape setup → Digest × C) =>
      rawEvent binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw pair.1
        ((byteCodec binary repr shape setup fits).oracle outside pair.2)).card : ℚ) /
        Fintype.card ((Fin TM → Digest) × (Point binary repr shape setup → Digest × C)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  have result := typed_ratio_le binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw
    layout hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits
    outside rawSampler hraw querySampler hquery hsupport hspace
  simpa only [raw_event_oracle binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw bodyFits] using result

include bodyFits hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits in
/-- The current 84-opening rate-1/7 bound for actual canonical byte query
inputs and finite ideal decoded answers. All verifier replay and extraction
correspondence is derived; coupling to SHAKE output bytes is outside this model. -/
theorem ratio_le
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R (wirePublic binary prime P R repr shape setup cfg)))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet 2443 84))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R (wirePublic binary prime P R repr shape setup cfg))
    (hsupport : ∀ (mt : Fin TM → Digest) (Hraw : Bytes → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) Hraw).card ≤ Q)
    (hspace : 4886+tA ≤ TM) (fallback : Bytes → Digest × C) :
    ((univ.filter fun pair : (Fin TM → Digest) ×
        ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} → Digest × C) =>
      rawEvent binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw pair.1
        (ByteOracleTransport.Codec.extendWindow
          (QueryRuntimeProbability.window repr shape setup binary.nPublic fits body) pair.2 fallback)).card : ℚ) /
        Fintype.card ((Fin TM → Digest) ×
          ({raw // raw ∈ QueryRuntimeProbability.window repr shape setup binary.nPublic fits body} → Digest × C)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  refine QueryRuntimeProbability.joint_ratio_le (M := Fin TM → Digest)
    repr shape setup binary.nPublic fits body dflt fallback
    (rawEvent binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw)
    (2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
      ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
        (Adapter.Mdoc.binaryOrder : ℚ)^2) ?_
  intro outside
  exact conditioned_ratio_le binary prime P R repr shape setup cfg binaryCount primeCount metadata fits body dflt draw
    layout hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits bodyFits
    outside rawSampler hraw querySampler hquery hsupport hspace

end LfzkV2.Current.CanonicalRate7
