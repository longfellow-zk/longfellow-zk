import LfzkV2.Current.RuntimeAdaptiveCommitment
import LfzkV2.Current.RuntimeShape
import LfzkV2.Current.RuntimeSamplers
import LfzkV2.Current.Parameters.Rate7

/-! The concrete rate-1/7 typed-runtime bound. One prime circuit plan and
one binary template determine every generated schedule. Public sampling laws
are fixed once; all coding and query-error bounds are derived. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveRate7
open Application ApplicationSetup ApplicationOracle RecursivePolygero Finset
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

local notation "profile" => FixedRate.Rate7.certificate
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]
variable [DecidableEq Enc] [DecidableEq Key]
variable {shared maskBits adviceBits tA calls Q TM : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B (profile).k (profile).s (profile).n (profile).t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) (profile).k (profile).s (profile).n (profile).t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → ZMod Adapter.Mdoc.primeOrder))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable (codec : Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
variable (dec : RoleDecoders codec) (dflt : Digest × C)
variable (body : TwoOracleTree Enc Digest
  (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))
  (Digest × C) (RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)) tA calls)
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)

/-- The selected private-cell source is fixed before later prime publics.
Only its recovered oracle changes with the Merkle tape. -/
abbrev source (mt : Fin TM → Digest) :=
  RuntimeAdaptiveCommitment.source profile binary prime P R cfg earlier codec dec dflt body layout mt

variable (samplers : RuntimeCover.SamplerLaws binary prime P R cfg
  (source binary prime P R cfg earlier codec dec dflt body layout (fun _ : Fin TM => 0)))
variable (primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (primeFits : primePlan.capacity ≤ samplers.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)
variable (binaryFits : binaryTemplate.capacity ≤ samplers.binaryCapacity)

include hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits in
/-- Complete typed-runtime extraction for 84 shared openings at rate 1/7.
Only the digest-sized remainder pays verifier replay. Requests and prime public inputs may be chosen adaptively; trusted circuit
metadata and the public parser remain fixed. -/
theorem ratio_le
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R cfg))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet 2443 84))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R cfg)
    (hsupport : ∀ (mt : Fin TM → Digest)
      (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
        (Base := Base) (Key := Key) → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) H).card ≤ Q)
    (hspace : 4886+tA ≤ TM) :
    ((univ.filter fun ω : (Fin TM → Digest) ×
        (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
          (Base := Base) (Key := Key) → Digest × C) =>
      RuntimeAdaptiveCommitment.Accepted profile binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body ω.1 ω.2 ∧
      RuntimeAdaptiveCommitment.ExtractionFailure profile binary prime P R cfg earlier hashPublic decodePublic draw codec dec dflt body ω.1 ω.2).card : ℚ) /
      ((Fintype.card Digest : ℚ)^TM*(Fintype.card (Digest × C) : ℚ)^Fintype.card
        (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator 4886 tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  exact RuntimeAdaptiveCommitment.ratio_le profile binary prime P R cfg earlier hashPublic decodePublic draw codec dec dflt body
    layout hlayout samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits
    rawSampler hraw querySampler hquery hsupport hspace

end LfzkV2.Current.RuntimeAdaptiveRate7
