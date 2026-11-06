import LfzkV2.Current.RuntimeAdaptiveReduction
import LfzkV2.Current.RuntimeParameters

/-! Adaptive runtime extraction with checked numerical profiles. The caller
supplies public circuits and uniform sampling interfaces; coding bounds,
selected-list caps and all local error budgets are derived here. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveProfileFS
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
variable (prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared)
variable (P : FieldBackend B c.k c.s c.n c.t)
variable (R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) c.k c.s c.n c.t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C) → Key → JointResponse.Oracle
    (RuntimeVerifier.first binary prime P R cfg).participant
    (RuntimeVerifier.second binary prime P R cfg).participant)
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
variable (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
  cutOracle H point.context = cutOracle H' point.context)
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → ZMod Adapter.Mdoc.primeOrder))
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg
  (RuntimeCover.source binary prime P R cfg layout c.cutoff cutOracle cutOff))
variable (primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)

local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields) (Advice := Advice) (Request := Request)

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]
variable [Nonempty C] [DecidableEq C] [DecidableEq Enc]
variable {tA calls Q TM : ℕ}

include laws primePlan primeGeometry primeFits binaryTemplate binaryGeometry binaryFits hlayout in
/-- The actual runtime failure event, with all coding and numerical
premises discharged by one certified profile. The batching sampler supplies
raw evaluations; the verifier fixes interpolation and physical row order. -/
theorem fs_ratio_le
    (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (rawSampler : BalancedDecoder C (RuntimeVerifier.RawSamples binary prime P R cfg))
    (hraw : rawSampler.decode = draw)
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet c.n c.t))
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R cfg)
    (body : TwoOracleTree Enc Digest Point (Digest × C) Output tA calls)
    (mt : Fin TM → Digest)
    (hsupport : ∀ H : Point → Digest × C,
      (TranscriptV2.seen (fixLeft mt default body []) H).card ≤ Q) :
    ((univ.filter fun H : Point → Digest × C =>
      RuntimeAdaptiveFS.Failure binary prime P R cfg earlier hashPublic decodePublic c.cutoff cutOracle draw codec
        ((fixLeft mt default body []).run H).1 H).card : ℚ) /
      (Fintype.card (Digest × C) : ℚ)^Fintype.card Point ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) + (4*Q+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  have hP : Nat.card (First).participant.Carrier = Adapter.Mdoc.binaryOrder := by
    change Nat.card B = Adapter.Mdoc.binaryOrder
    simpa only [Nat.card_eq_fintype_card] using cfg.card
  have hR : Nat.card (Second).participant.Carrier = Adapter.Mdoc.primeOrder := by
    change Nat.card (ZMod Adapter.Mdoc.primeOrder) = Adapter.Mdoc.primeOrder
    simp only [Nat.card_eq_fintype_card,ZMod.card]
  let pc := c.parameters (First).participant.backend (First).participant.columns
    (First).participant.dimension (First).participant.batching (First).participant.openings (Or.inl hP)
  let rc := c.parameters (Second).participant.backend (Second).participant.columns
    (Second).participant.dimension (Second).participant.batching (Second).participant.openings (Or.inr hR)
  have hbound : pc.listBound ≤ Nat.card (First).participant.Carrier := by
    change c.activeList ≤ Nat.card (First).participant.Carrier
    rw [hP]
    exact c.active_list_le_field
  have hactive : CodingTheory.UniformFamilyBound c.n pc.columnCutoff (c.k+2*c.s-1) pc.listBound :=
    c.active_bound
  have hparent : pc.rankError+rc.rankError+
      JointResponse.activeHighBudget (First).participant (Second).participant pc ≤
      1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) :=
    c.parameters_parent_budget_le (First).participant (Second).participant hP hR
  have hopening : GlobalCharges.openingBudget (s := c.s) (n := c.n) (t := c.t)
      c.cutoff c.threshold ≤ 1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) := by
    change ParameterBounds.openingBudget c.n c.s c.t c.activeCutoff c.binaryCutoff c.primeCutoff ≤ _
    exact c.opening_budget_le
  have hbudget : 1999999/(1000000*(Adapter.Mdoc.binaryOrder:ℚ)) ≤
      2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ) := by
    norm_num [Adapter.Mdoc.binaryOrder]
  let coinSampler := BackendChallenges.decoder P R cfg.countBinary cfg.countPrime
    (RuntimeVerifier.rowPositive binary prime P R cfg) rawSampler
  have hcoin : coinSampler.decode = RuntimeVerifier.batchingDecoder binary prime P R cfg draw := by
    funext answer
    change BackendChallenges.pairEquiv P R cfg.countBinary cfg.countPrime
      (RuntimeVerifier.rowPositive binary prime P R cfg) (rawSampler.decode answer) = _
    rw [hraw]
    rfl
  exact RuntimeAdaptiveFS.fs_ratio_le binary prime P R cfg earlier hashPublic decodePublic layout c.cutoff cutOracle cutOff
    laws primePlan primeFits binaryTemplate binaryFits draw hlayout primeGeometry binaryGeometry
    (fun point H => RuntimeParameters.binary_list_card c binary prime P R cfg layout cutOracle cutOff
      point.context ((RuntimeCover.source binary prime P R cfg layout c.cutoff cutOracle cutOff).oracle H point.context))
    (fun point H => RuntimeParameters.prime_list_card c binary prime P R cfg layout cutOracle cutOff
      point.context ((RuntimeCover.source binary prime P R cfg layout c.cutoff cutOracle cutOff).oracle H point.context))
    c.threshold codec coinSampler querySampler hcoin hquery pc rc.toProfileParameters le_rfl hactive hbound
    (c.round_budget_le cfg.card) (hparent.trans hbudget) (hopening.trans hbudget) body mt hsupport

end LfzkV2.Current.RuntimeAdaptiveProfileFS
