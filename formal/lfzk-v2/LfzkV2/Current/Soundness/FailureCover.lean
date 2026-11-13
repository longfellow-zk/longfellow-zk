import LfzkV2.Current.Soundness.RuntimeCharges
import LfzkV2.Current.RuntimeAdaptiveAccepted

/-! Shared adaptive Fiat–Shamir reduction from actual runtime acceptance.
The leading query budget is that of the original prover, across every
request branch, rather than a sum of fixed-public experiments. -/
noncomputable section
namespace LfzkV2.Current.Soundness.RuntimeCharges
open Application ApplicationSetup ApplicationOracle RecursivePolygero ProfileAnalysis Finset
open Merkle.RandomOracle
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
local notation "Generator" => cfg.polynomialX^Adapter.Mdoc.generatorExponent
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
local notation "S" => RuntimeSource.source binary prime P R cfg layout cutoff cutOracle cutOff
variable (laws : RuntimeSource.SamplerLaws binary prime P R cfg
  (RuntimeSource.source binary prime P R cfg layout cutoff cutOracle cutOff))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.circuit)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "readers" => RuntimeAdaptiveCharges.concreteReaders S laws hashPublic decodePublic
  primePlan primeFits binaryTemplate binaryFits

variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

variable (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
variable (primeGeometry : primePlan.frontend = g.prime)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)

include hlayout primeGeometry binaryGeometry in
/-- The algebraic cover uses the decoded application and the explained
joint opening, independently of the transcript's final-seal construction.
It reconstructs the common selected witness from the actual prefix. The
transcript realization must separately supply query membership and order. -/
theorem decoded_charge_cover (epsilon : ℚ) (output : Output) (H : Point → Digest × C)
    (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded)
    (hverify : let auth := RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded
      JointResponse.Verify (First).participant (Second).participant auth.statement auth.oracle auth.coin auth.response decoded.query)
    (hfailure : ¬ ∃ w, (RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).context.extract =
      some w ∧ decoded.application.True w) :
    let charge := single laws readers (RuntimeVerifier.encodeResponses binary prime P R cfg)
      (RuntimeAdaptiveBackend.derive binary prime P R cfg hashPublic decodePublic)
      (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
      (RuntimeVerifier.queryDecoder binary prime P R cfg) cutoff epsilon
    let pairCharge := pair («S» := S) (RuntimeAdaptiveBackend.derive binary prime P R cfg hashPublic decodePublic)
      (RuntimeVerifier.batchingDecoder binary prime P R cfg draw)
      (RuntimeVerifier.queryDecoder binary prime P R cfg) epsilon
    (∃ i < g.roles.length, 1 ≤ charge ((M).point output H i) H (H ((M).point output H i))) ∨
      (∃ i < g.roles.length, ∃ parent response,
        parent.point = (M).point output H i ∧
        parent.child g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg) response = (M).point output H (i+1) ∧
        1 ≤ pairCharge parent response H (H parent.point)
          (H (parent.child g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg) response))) := by
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
        simpa only [BackendOracle.single_point,RuntimeSource.source,ZkJoint.JointParam.source] using hb
      · refine Or.inl ⟨g.openingIndex.val,g.openingIndex.isLt,?_⟩
        apply backend_charged laws readers _ _ _ _ cutoff epsilon
        rw [ho,BackendOracle.single_child (First).participant (Second).participant
          g.batchingIndex_next (RuntimeVerifier.encodeResponses binary prime P R cfg)
          (RuntimeVerifier.encodeResponses_injective binary prime P R cfg)]
        rw [ho] at hb
        simpa only [RuntimeSource.source,ZkJoint.JointParam.source] using hb
      · refine Or.inr ⟨g.batchingIndex.val,g.batchingIndex.isLt,parent,response,hp,?_,?_⟩
        · rw [← ho,g.openingIndex_val]
        · change 1 ≤ BackendFS.high (First).participant (Second).participant _ _ _ _ _ _ _ _ _ _
          rw [← ho]
          exact hb
    · exact Or.inl ⟨index,hindex,application_charged laws readers _ _ _ _ cutoff epsilon _ H _ hcharged⟩

end LfzkV2.Current.Soundness.RuntimeCharges
