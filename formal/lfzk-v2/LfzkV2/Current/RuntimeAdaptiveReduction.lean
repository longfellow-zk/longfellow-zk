import LfzkV2.Current.RuntimeAdaptiveFS
import LfzkV2.Current.RuntimeAdaptiveAccepted

/-! Shared adaptive Fiat–Shamir reduction from actual runtime acceptance.
The leading query budget is that of the original prover, across every
request branch, rather than a sum of fixed-public experiments. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveFS
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Decoded" => RuntimeVerifier.Decoded binary prime P R cfg
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) C)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (cutoff : ℕ × ℕ)
variable (cutOracle : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C) → Key → JointResponse.Oracle
    (RuntimeVerifier.first binary prime P R cfg).participant
    (RuntimeVerifier.second binary prime P R cfg).participant)
variable (cutOff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
  cutOracle H point.context = cutOracle H' point.context)
local notation "S" => RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg
  (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "readers" => RuntimeAdaptiveCharges.concreteReaders S laws hashPublic decodePublic
  primePlan primeFits binaryTemplate binaryFits

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

/-- After the single joint tuple opening is explained, the remaining
failure is exactly that of the actual adaptive runtime decoder. -/
def Failure (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (output : Output) (H : Point → Digest × C) : Prop :=
  ∃ (HM : Enc → Digest) (decoded : Decoded),
    RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded ∧
    RuntimeAdaptiveVerifier.Checks binary prime P R cfg earlier codec HM output H decoded ∧
    (let auth := RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded
     JointResponse.Verify (First).participant (Second).participant auth.statement auth.oracle auth.coin auth.response decoded.query) ∧
    ¬ ∃ w, (RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).context.extract =
      some w ∧ decoded.application.True w

variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)

/-- The failure cover is reconstructed from the accepted prefix. In
particular no execution or local-coverage certificate is supplied. -/
def reduction (epsilon : ℚ)
    (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc) :
    TranscriptV2.SharedReduction (M)
      (fun parent : BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex => parent.point)
      (fun parent response => parent.child g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg) response)
      (single laws readers (RuntimeVerifier.encodeResponses binary prime P R cfg)
        (RuntimeAdaptiveBackend.derive binary prime P R cfg hashPublic decodePublic)
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
        (RuntimeBackend.queryDecoder binary prime P R cfg) cutoff epsilon)
      (pair («S» := S) (RuntimeAdaptiveBackend.derive binary prime P R cfg hashPublic decodePublic)
        (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
        (RuntimeBackend.queryDecoder binary prime P R cfg) epsilon)
      (Failure binary prime P R cfg earlier hashPublic decodePublic cutoff cutOracle draw codec) where
  cover output H h := by
    obtain ⟨_,decoded,hd,_,hverify,hfailure⟩ := h
    have hcover := RuntimeAdaptiveAccepted.decoded_failure_cover binary prime P R cfg earlier hashPublic decodePublic layout
      cutoff cutOracle cutOff laws primePlan primeFits binaryTemplate binaryFits hlayout primeGeometry binaryGeometry
      draw output H decoded hd hfailure
    rcases hcover with hbackend | ⟨index,hindex,hcharged⟩
    · have hb := RuntimeAdaptiveBackend.failure_charged binary prime P R cfg earlier hashPublic decodePublic draw cutOracle cutoff epsilon
        output H decoded hd hverify hbackend
      let e := encodings output.request
      let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
      let response := ((H parent.point).1,RuntimeVerifier.responses binary prime P R cfg output.proof)
      have hp : parent.point = (M).point output H g.batchingIndex.val := by
        rw [RuntimeAdaptiveVerifier.point_eq]
        exact BackendPath.parent_point e cfg.initialLink output.proof H g.batchingIndex
      have ho := RuntimeAdaptiveBackend.opening_eq binary prime P R cfg earlier output H
      rcases hb with hb | hb | hb
      · refine Or.inl ⟨g.batchingIndex.val,g.batchingIndex.isLt,?_⟩
        rw [← hp]
        apply backend_charged laws readers _ _ _ _ cutoff epsilon
        simpa only [BackendOracle.single_point,RuntimeCover.source,ZkJoint.JointParam.source] using hb
      · refine Or.inl ⟨g.openingIndex.val,g.openingIndex.isLt,?_⟩
        apply backend_charged laws readers _ _ _ _ cutoff epsilon
        rw [ho,BackendOracle.single_child (First).participant (Second).participant
          g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
          (RuntimeVerifier.encodeResponses_injective binary prime P R cfg)]
        rw [ho] at hb
        simpa only [RuntimeCover.source,ZkJoint.JointParam.source] using hb
      · refine Or.inr ⟨g.batchingIndex.val,g.batchingIndex.isLt,parent,response,hp,?_,?_⟩
        · rw [← ho,g.openingIndex_val]
        · change 1 ≤ BackendFS.high (First).participant (Second).participant _ _ _ _ _ _ _ _ _ _
          rw [← ho]
          exact hb
    · exact Or.inl ⟨index,hindex,application_charged laws readers _ _ _ _ cutoff epsilon _ H _ hcharged⟩
  final_seal_valid output H h := by
    obtain ⟨_,_,_,hchecks,_,_⟩ := h
    exact hchecks.2.2.2

variable {LB LN : ℕ}
variable (binaryListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  ((RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).lists point.context
    ((RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).oracle H point.context)).1.card ≤ LB)
variable (primeListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  ((RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).lists point.context
    ((RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff).oracle H point.context)).2.card ≤ LN)

variable [Fintype Key] [Fintype Base] [Fintype Advice] [∀ side, Fintype (fields side)]
variable [Nonempty C] [DecidableEq C] [DecidableEq Enc]
variable {tA calls Q TM : ℕ}

include laws primePlan primeFits binaryTemplate binaryFits hlayout primeGeometry binaryGeometry binaryListBound primeListBound in
/-- Distinct-query extractor soundness for the concrete runtime's decoded
failure event. All charge coverage comes from the successful parser; public
sampling laws and checked numerical coding budgets are the only bounds. -/
theorem fs_ratio_le
    (epsilon : ℚ)
    (codec : Merkle.MH.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
    (coinSampler : BalancedDecoder C (JointResponse.Coin (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant))
    (querySampler : BalancedDecoder C (LigeroFamily.QuerySet n t))
    (hcoin : coinSampler.decode = RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
    (hquery : querySampler.decode = RuntimeBackend.queryDecoder binary prime P R cfg)
    (pc : HahnSystemCertificate (RuntimeVerifier.first binary prime P R cfg).participant.backend) (rc : ProfileParameters (RuntimeVerifier.second binary prime P R cfg).participant.backend)
    (hθ : pc.threshold ≤ epsilon)
    (hactive : CodingTheory.UniformFamilyBound n pc.columnCutoff (k+2*s-1) pc.listBound)
    (hbound : pc.listBound ≤ Nat.card (RuntimeVerifier.first binary prime P R cfg).participant.Carrier)
    (happ : ∀ role, ApplicationCharging.roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound LB LN role ≤ 2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (hparent : pc.rankError+rc.rankError+JointResponse.activeHighBudget (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant pc ≤
      2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (hopening : GlobalCharges.openingBudget (s := s) (n := n) (t := t) cutoff epsilon ≤
      2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (body : TwoOracleTree Enc Digest (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) (Digest × C) Output tA calls)
    (mt : Fin TM → Digest)
    (hsupport : ∀ H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C,
      (TranscriptV2.seen (fixLeft mt default body []) H).card ≤ Q) :
    ((univ.filter fun H : (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) → Digest × C =>
      Failure binary prime P R cfg earlier hashPublic decodePublic cutoff cutOracle draw codec
        ((fixLeft mt default body []).run H).1 H).card : ℚ) /
      (Fintype.card (Digest × C) : ℚ)^Fintype.card (RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key)) ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) + (4*Q+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  let encode := RuntimeVerifier.encodeResponses binary prime P R cfg
  let derive := RuntimeAdaptiveBackend.derive binary prime P R cfg hashPublic decodePublic
  let decodeCoin := RuntimeVerifier.batchingDecoder binary prime P R cfg draw
  let decodeQuery := RuntimeBackend.queryDecoder binary prime P R cfg
  have hencode := RuntimeVerifier.encodeResponses_injective binary prime P R cfg
  exact ChainedFS.ratio_le_support
    (M) body
    (fun parent : (BackendQueries.Parent g.roles Key (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := Base)) Digest g.batchingIndex) => parent.point)
    (fun parent response => parent.child g.batchingIndex_next encode response)
    (single laws readers encode derive decodeCoin decodeQuery cutoff epsilon)
    (pair («S» := S) derive decodeCoin decodeQuery epsilon)
    (Failure binary prime P R cfg earlier hashPublic decodePublic cutoff cutOracle draw codec)
    (reduction binary prime P R cfg earlier hashPublic decodePublic layout cutoff cutOracle cutOff laws primePlan primeFits binaryTemplate binaryFits draw hlayout primeGeometry binaryGeometry epsilon codec)
    (fun parent response => parent.point_ne_child g.batchingIndex_next encode response)
    (single_off laws readers encode derive decodeCoin decodeQuery cutoff epsilon hencode)
    (single_nonneg laws readers encode derive decodeCoin decodeQuery cutoff epsilon)
    (pair_off encode derive decodeCoin decodeQuery epsilon)
    (pair_nonneg («S» := S) derive decodeCoin decodeQuery epsilon)
    (budget (LB := LB) (LN := LN) encode cutoff epsilon pc.toProfileParameters rc)
    (fun _ => JointResponse.activeHighBudget (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant pc)
    (single_sum laws readers encode derive decodeCoin decodeQuery cutoff epsilon binaryListBound primeListBound coinSampler querySampler
      hcoin hquery pc.toProfileParameters rc (pc.threshold_nonneg.trans hθ))
    (pair_sum («S» := S) derive decodeCoin decodeQuery epsilon coinSampler querySampler hcoin hquery
      pc rc hθ hactive hbound)
    (point_budget_le (LB := LB) (LN := LN) encode cutoff epsilon hencode pc.toProfileParameters rc
      (JointResponse.activeHighBudget (RuntimeVerifier.first binary prime P R cfg).participant (RuntimeVerifier.second binary prime P R cfg).participant pc) (2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
      happ hparent hopening (by positivity)) mt hsupport

end LfzkV2.Current.RuntimeAdaptiveFS
