import LfzkV2.Current.RuntimeAdaptiveProfileFS
import LfzkV2.Current.RuntimeAdaptiveSupport
import LfzkV2.Current.RuntimeSamplers

/-! Complete extractor soundness from actual runtime acceptance. One
canonical tuple opening is explained once. The final seal and decoded
arithmetic checks are then charged to the original program's distinct
transcript queries, with no execution or correspondence certificate. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveCommitment
open Application ApplicationSetup ApplicationOracle RecursivePolygero Finset
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]
variable [DecidableEq Enc] [DecidableEq Key]
variable {shared maskBits adviceBits tA calls Q TM : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B c.k c.s c.n c.t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) c.k c.s c.n c.t)
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
variable (body : TwoOracleTree Enc Digest (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) (Digest × C) (RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)) tA calls)

/-- Recover the two committed fields together from the trace at the first
query naming their common context. No frontend sumcheck is run by this cut. -/
def cutOracle (mt : Fin TM → Digest) : ((RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) → Key →
    JointResponse.Oracle (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant :=
  RuntimeAdaptiveMerkle.cutOracle binary prime P R cfg earlier codec dflt body dec mt

omit [Fintype C] [Nonempty C] [DecidableEq C] [Fintype Key] [Fintype Base] [Fintype Advice]
  [∀ side, Fintype (fields side)] in
theorem cutOracle_off (mt : Fin TM → Digest) (point : RuntimeVerifier.Point (g := g) (fields := fields)
    (Advice := Advice) (Base := Base) (Key := Key))
    (H H' : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') :
    cutOracle c binary prime P R cfg earlier codec dec dflt body mt H point.context =
      cutOracle c binary prime P R cfg earlier codec dec dflt body mt H' point.context :=
  RuntimeAdaptiveMerkle.cutOracle_off binary prime P R cfg earlier codec dflt body dec mt point H H' h

/-- Acceptance is the concrete Boolean verifier on the original proof.
Its oracle is the actual one-tree Merkle experiment, not an independently
supplied compiled-acceptance predicate. -/
def Accepted (mt : Fin TM → Digest) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) : Prop :=
  RuntimeAdaptiveVerifier.verify binary prime P R cfg earlier hashPublic decodePublic draw codec
    (RuntimeAdaptiveMerkle.merkleOracle binary prime P R cfg earlier codec dflt body mt H)
    (RuntimeAdaptiveMerkle.originalOutput body mt H) H = true

/-- The extracted full-cell pair must satisfy the decoded application.
Late authentication selects the same pair as the early fingerprint boundary;
that equality is derived by `RuntimeSelection.selected_of_decode`. -/
def ExtractionFailure (mt : Fin TM → Digest) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) : Prop :=
  ∀ decoded, RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw (RuntimeAdaptiveMerkle.originalOutput body mt H) H = some decoded →
    ¬ ∃ w, (RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier
      (cutOracle c binary prime P R cfg earlier codec dec dflt body mt) c.cutoff
      (RuntimeAdaptiveMerkle.originalOutput body mt H) H decoded).context.extract = some w ∧
      decoded.application.True w

variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
/-- One fixed sampler interface suffices across every request and Merkle
tape: only the recovered oracle changes, while coin maps stay identical. -/
def source (mt : Fin TM → Digest) :=
  RuntimeCover.source binary prime P R cfg layout c.cutoff
    (cutOracle c binary prime P R cfg earlier codec dec dflt body mt)
    (cutOracle_off c binary prime P R cfg earlier codec dec dflt body mt)

omit [Fintype C] [Nonempty C] [DecidableEq C] [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)] in
/-- The fingerprint decoder is public setup data. Recovering a commitment
oracle or changing the prover program cannot change this projection. -/
theorem source_coins (mt : Fin TM → Digest) :
    (source c binary prime P R cfg earlier codec dec dflt body layout mt).coins =
      fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer) := rfl

variable (samplers : RuntimeCover.SamplerLaws binary prime P R cfg
  (source c binary prime P R cfg earlier codec dec dflt body layout (fun _ : Fin TM => 0)))
variable (primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (primeFits : primePlan.capacity ≤ samplers.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)
variable (binaryFits : binaryTemplate.capacity ≤ samplers.binaryCapacity)

def samplingAt (mt : Fin TM → Digest) : RuntimeCover.SamplerLaws binary prime P R cfg
    (source c binary prime P R cfg earlier codec dec dflt body layout mt) :=
  samplers.retarget (source c binary prime P R cfg earlier codec dec dflt body layout mt) (by rfl)

include samplers primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits hlayout in
/-- Complete accepted-failure bound with checked coding parameters and one
shared Merkle explanation. Only its digest-sized remainder pays verifier
replay; Q counts distinct inputs queried by the original program. -/
theorem ratio_le
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R cfg))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet c.n c.t))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R cfg)
    (hsupport : ∀ (mt : Fin TM → Digest) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C),
      (TranscriptV2.seen (fixLeft mt default body []) H).card ≤ Q)
    (hspace : 2*c.n+tA ≤ TM) :
    ((univ.filter fun ω : (Fin TM → Digest) × ((RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) =>
      Accepted c binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body ω.1 ω.2 ∧
      ExtractionFailure c binary prime P R cfg earlier hashPublic decodePublic draw codec dec dflt body ω.1 ω.2).card : ℚ) /
      ((Fintype.card Digest : ℚ)^TM*(Fintype.card (Digest × C) : ℚ)^Fintype.card (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key))) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        ((4*Q+1+Bcs.AdaptiveCommit.adaptiveNumerator (2*c.n) tA (1+g.roles.length+Q) : ℕ) : ℚ) /
          (Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  let accepted := fun (mt : Fin TM → Digest) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) =>
    Accepted c binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body mt H
  let fails := fun (mt : Fin TM → Digest) (H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C) =>
    ExtractionFailure c binary prime P R cfg earlier hashPublic decodePublic draw codec dec dflt body mt H
  let ideal := fun (mt : Fin TM → Digest) proof H => RuntimeAdaptiveFS.Failure binary prime P R cfg earlier hashPublic decodePublic c.cutoff
    (cutOracle c binary prime P R cfg earlier codec dec dflt body mt) draw codec proof H
  have hfs (mt : Fin TM → Digest) :
      ((univ.filter fun H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C =>
        ideal mt ((fixLeft mt default body []).run H).1 H).card : ℚ) /
        (Fintype.card (Digest × C) : ℚ)^Fintype.card (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ)+(4*Q+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2 := by
    exact RuntimeAdaptiveProfileFS.fs_ratio_le c binary prime P R cfg draw
      (cutOracle c binary prime P R cfg earlier codec dec dflt body mt) layout hlayout
      (cutOracle_off c binary prime P R cfg earlier codec dec dflt body mt) earlier hashPublic decodePublic
      (samplingAt c binary prime P R cfg earlier codec dec dflt body layout samplers mt)
      primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits
      codec rawSampler hraw querySampler hquery body mt (hsupport mt)
  have hn : 0 < c.n := by
    have := c.positive_degree
    have := c.large_le_active
    have := c.active_le_columns
    omega
  have hbound := RuntimeAdaptiveMerkle.ratio_le_support binary prime P R cfg earlier dflt body hsupport codec dec
    (RuntimeAdaptiveMerkle.check binary prime P R cfg codec) cfg.root (RuntimeAdaptiveMerkle.claimOf binary prime P R cfg)
    (CommitmentOracle.check_contains codec (RuntimeAdaptiveMerkle.claimOf binary prime P R cfg))
    (by omega) hspace (by omega) accepted fails
    (by
      intro mt H ha
      obtain ⟨decoded,hd,hc⟩ :=
        (RuntimeAdaptiveVerifier.verify_true_iff binary prime P R cfg earlier hashPublic decodePublic draw codec
          (RuntimeAdaptiveMerkle.merkleOracle binary prime P R cfg earlier codec dflt body mt H)
          (RuntimeAdaptiveMerkle.originalOutput body mt H) H).mp ha
      exact RuntimeAdaptiveMerkle.merkle_accepts binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body mt H decoded hd hc)
    ideal
    (by
      intro mt H ha he hf
      obtain ⟨decoded,hd,hc⟩ :=
        (RuntimeAdaptiveVerifier.verify_true_iff binary prime P R cfg earlier hashPublic decodePublic draw codec
          (RuntimeAdaptiveMerkle.merkleOracle binary prime P R cfg earlier codec dflt body mt H)
          (RuntimeAdaptiveMerkle.originalOutput body mt H) H).mp ha
      have hv := RuntimeAdaptiveMerkle.verify_of_explains binary prime P R cfg earlier hashPublic decodePublic draw codec dflt body dec
        mt H decoded hd hc he
      rw [RuntimeAdaptiveMerkle.proof_eq]
      change RuntimeAdaptiveFS.Failure binary prime P R cfg earlier hashPublic decodePublic c.cutoff
        (cutOracle c binary prime P R cfg earlier codec dec dflt body mt) draw codec
        (RuntimeAdaptiveMerkle.originalOutput body mt H) H
      exact ⟨_,decoded,hd,hc,hv,hf decoded hd⟩)
    (2*Q/(Adapter.Mdoc.binaryOrder : ℚ)+(4*Q+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2) hfs
  exact hbound.trans_eq (by rw [ChainedFS.digest_card,Nat.cast_pow]; push_cast; ring)

end LfzkV2.Current.RuntimeAdaptiveCommitment
