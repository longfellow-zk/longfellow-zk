import LfzkV2.Current.RuntimeAdaptiveStatement
import LfzkV2.Current.RuntimeAdaptiveRoles
import LfzkV2.Current.RuntimeAdaptiveLocal
import LfzkV2.Current.RuntimeAdaptiveBatch
import LfzkV2.Current.RuntimeAdaptiveAuxiliary
import LfzkV2.Current.RuntimeAdaptiveBackend

/-! The causal failure cover for adaptive runtime requests. Public values are
read from the actual prefix where they are bound; all local charges belong
to one query space and the same early-selected private pair. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveAccepted
open RuntimeAdaptive RuntimeCover ApplicationViews ApplicationOracle Application ApplicationSetup RecursivePolygero SumcheckV2
open scoped Classical

private theorem indicator_charged {event : Prop} (h : event) : 1 ≤ indicator event := by
  simp only [indicator,if_pos h,le_refl]

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Request : Type}
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
local notation "S" => RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg
  (RuntimeCover.source binary prime P R cfg layout cutoff cutOracle cutOff))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "readers" => RuntimeAdaptiveCharges.concreteReaders S laws hashPublic decodePublic
  primePlan primeFits binaryTemplate binaryFits

def Charged (output : Output) (H : Point → Digest × C) : Prop :=
  ∃ index < g.roles.length,
    1 ≤ RuntimeAdaptiveCharges.single S laws readers ((M).point output H index) H
      (H ((M).point output H index))

section Parsed
variable (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
local notation "currentBinary" => binaryWithBits binary bits
local notation "currentPrime" => primeWithInputs prime inputs

/-- The six actual parsed algebraic events, without introducing a new
configuration for the adaptively read public inputs. -/
def ParsedBad (nd : PrimeData currentPrime C) (bd : BinaryData currentBinary nd Generator) (w : Pair) : Prop :=
  (∃ query < FrontendReplay.slots bd.setup.circuit,
    FrontendReplay.BadAt bd.decode bd.nonzero bd.setup.circuit bd.setup.plan bd.payload bd.answers
      ((currentBinary).inputs (binaryValues currentBinary currentPrime w))
      (fun i => binaryValues currentBinary currentPrime w (CellLayout.Binary.pad binary.words binary.degree binary.pads i)) query) ∨
  bd.frontend.source.Bad (binaryValues currentBinary currentPrime w) bd.U bd.delta ∨
  (∃ query < FrontendReplay.slots prime.circuit,
    FrontendReplay.BadAt nd.decode nd.nonzero prime.circuit prime.setup.plan nd.payload nd.answers
      (primeInputs currentBinary currentPrime w)
      (fun i => primeFullValues currentBinary currentPrime w (.inr (CellLayout.Prime.pad prime.remaining prime.pads i))) query) ∨
  Prime.BatchBad (fun i => (nd.frontend.rows.get i).eval (primeFullValues currentBinary currentPrime w)) nd.rho ∨
  Prime.RescalingBad
    (nd.claim.residual (fun i => if (currentBinary).sharedValues w.1 i then 1 else 0)
      (fun i => primeValues currentBinary currentPrime w (.inl i)))
    (Handoff.binaryMask ((currentBinary).mask w.1) - primeValues currentBinary currentPrime w (.inr ())) bd.eta ∨
  Handoff.ConversionBad nd.claim.sharedWeights bd.eta bd.mu
    ((currentBinary).sharedValues w.1) ((currentBinary).mask w.1) Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound bd.alpha

omit [Fintype C] in
theorem parsedBad_iff (nd : PrimeData currentPrime C) (bd : BinaryData currentBinary nd Generator)
    (A : RuntimeVerifier.System binary prime (C := C))
    (h : ApplicationSetup.decodeChecked currentBinary currentPrime nd cfg.card cfg.polynomialX cfg.quotientBound bd = some A)
    (w : Pair) : A.Bad w ↔ ParsedBad binary prime P R cfg bits inputs nd bd w := by
  unfold ApplicationSetup.decodeChecked at h
  split at h
  · unfold ApplicationSetup.decode at h
    split at h
    · cases Option.some.inj h
      rfl
    · contradiction
  · contradiction
end Parsed

theorem parsed_charged
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (primeGeometry : primePlan.frontend = g.prime)
    (binaryGeometry : binaryTemplate.frontend = g.binary)
    (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hstatement : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
      (((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val)
      ((((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val).priorAnswers H) =
      some ⟨decoded.application,decoded.statement⟩)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      (((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hprime : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback
      (((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val)
      ((((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val).priorAnswers H) = some nd)
    (hbinary : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree cfg.binaryField cfg.primeField
      cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
      (((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val)
      ((((encodings output.request).chain cfg.initialLink).point output.proof H g.batchingIndex.val).priorAnswers H) = some bd)
    (w : Pair)
    (hselected : (RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).context.extract = some w)
    (hbad : ParsedBad binary prime P R cfg bits inputs nd bd w) :
    Charged binary prime P R cfg earlier hashPublic decodePublic layout cutoff cutOracle cutOff laws
      primePlan primeFits binaryTemplate binaryFits output H := by
  let e := encodings output.request
  have selected (index : ℕ) (hi : index < g.roles.length) (hpos : 0 < index) :
      (S).selected ((e.chain cfg.initialLink).point output.proof H index) H = some w :=
    (RuntimeAdaptiveStatement.selected_on_replay binary prime P R cfg hashPublic decodePublic layout hlayout cutoff cutOracle cutOff
      e cfg.initialLink output.proof H index g.batchingIndex.val hi.le g.batchingIndex.isLt.le hpos
      (by simp only [Geometry.batchingIndex_val,Geometry.backendPrefix,List.length_append,List.length_cons,List.length_nil]; omega)
      ⟨decoded.application,decoded.statement⟩ hstatement decoded.coin (RuntimeVerifier.responses binary prime P R cfg output.proof)).trans hselected
  have primeWindow : FrontendReplay.slots prime.circuit = (g.prime.roles .prime).length := by
    rw [primePlan.slots_eq_roles_length .prime,primeGeometry]
  let packet : AdapterPacket (binaryWithBits binary bits) (primeWithInputs prime inputs) C := ⟨nd,bd.eta,bd.mu,bd.alpha,bd.masked⟩
  have binaryWindow : FrontendReplay.slots bd.setup.circuit = (g.binary.roles .binary).length := by
    have hh := (RuntimeShape.binaryPlan (binaryWithBits binary bits) (primeWithInputs prime inputs) Generator binaryTemplate packet).slots_eq_roles_length .binary
    rw [RuntimeShape.binaryPlan_frontend] at hh
    change FrontendReplay.slots bd.setup.circuit = (binaryTemplate.frontend.roles .binary).length at hh
    rwa [binaryGeometry] at hh
  have hn : ApplicationPrefix.rowBatchingIndex g < g.roles.length := by
    have hh := g.roles_length
    simp only [ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *; omega
  have hr : ApplicationPrefix.rescalingIndex g < g.roles.length := by
    have hh := g.roles_length
    simp only [ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *; omega
  have hc : ApplicationPrefix.conversionIndex g < g.roles.length := by
    have hh := g.roles_length
    simp only [ApplicationPrefix.conversionIndex,ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *; omega
  have hp : ApplicationPrefix.packingIndex g < g.roles.length := by
    have hh := g.roles_length
    simp only [ApplicationPrefix.packingIndex,Geometry.binaryStart] at *; omega
  rcases hbad with ⟨query,hquery,hbad⟩ | hbad | ⟨query,hquery,hbad⟩ | hbad | hbad | hbad
  · have hi : g.binaryStart+query < g.roles.length := by
      have hh := g.roles_length; have hqq := hquery
      rw [binaryWindow] at hqq; dsimp only [Geometry.binaryStart]; omega
    have hlocal := RuntimeAdaptiveLocal.binary_bad binary prime P R cfg S laws hashPublic decodePublic primePlan
      binaryTemplate binaryFits e cfg.initialLink output.proof H primeGeometry g.batchingIndex.val g.batchingIndex.isLt.le
      bits inputs hpublic nd bd hprime hbinary query hquery w (selected _ hi (by have := g.binaryStart_pos; omega)) hbad
    refine ⟨g.binaryStart+query,hi,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq]
    rw [RuntimeAdaptiveRoles.binary_single binary prime P R cfg S laws binaryTemplate e cfg.initialLink output.proof H readers
      binaryGeometry bits inputs packet query hquery]
    exact indicator_charged hlocal
  · have hlocal := RuntimeAdaptiveAuxiliary.packing_of_late laws hashPublic decodePublic primePlan primeGeometry e cfg.initialLink
      output.proof H binaryTemplate binaryGeometry g.batchingIndex.val g.batchingIndex.isLt.le bits inputs hpublic nd bd hprime hbinary
      w (selected _ hp (by dsimp only [ApplicationPrefix.packingIndex,Geometry.binaryStart]; omega)) hbad
    refine ⟨ApplicationPrefix.packingIndex g,hp,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.packing_single binary prime P R cfg S laws e cfg.initialLink output.proof H readers]
    exact indicator_charged hlocal
  · have hi : g.primeStart+query < g.roles.length := by
      have hh := g.roles_length; have hqq := hquery
      rw [primeWindow] at hqq; dsimp only [Geometry.primeStart]; omega
    have hlocal := RuntimeAdaptiveLocal.prime_bad binary prime P R cfg S laws hashPublic decodePublic primePlan primeFits
      e cfg.initialLink output.proof H g.batchingIndex.val g.batchingIndex.isLt.le bits inputs hpublic nd hprime query hquery w
      (selected _ hi (by have := g.primeStart_pos; omega)) hbad
    refine ⟨g.primeStart+query,hi,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.prime_single binary prime P R cfg S laws primePlan e cfg.initialLink output.proof H readers primeGeometry query hquery]
    exact indicator_charged hlocal
  · have hlocal := RuntimeAdaptiveBatch.batch_of_late binary prime P R cfg S laws hashPublic decodePublic primePlan e cfg.initialLink
      output.proof H primeGeometry g.batchingIndex.val g.batchingIndex.isLt.le bits inputs hpublic nd hprime w
      (selected _ hn (by dsimp only [ApplicationPrefix.rowBatchingIndex,Geometry.primeStart]; omega)) hbad
    refine ⟨ApplicationPrefix.rowBatchingIndex g,hn,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.rowBatching_single binary prime P R cfg S laws e cfg.initialLink output.proof H readers]
    exact indicator_charged hlocal
  · have hlocal := RuntimeAdaptiveBatch.rescale_of_late binary prime P R cfg S laws hashPublic decodePublic primePlan e cfg.initialLink
      output.proof H primeGeometry g.batchingIndex.val g.batchingIndex.isLt.le bits inputs hpublic nd bd hprime hbinary w
      (selected _ hr (by dsimp only [ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart]; omega)) hbad
    refine ⟨ApplicationPrefix.rescalingIndex g,hr,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.rescaling_single binary prime P R cfg S laws e cfg.initialLink output.proof H readers]
    exact indicator_charged hlocal
  · have hlocal := RuntimeAdaptiveAuxiliary.conversion_of_late laws hashPublic decodePublic primePlan primeGeometry e cfg.initialLink
      output.proof H g.batchingIndex.val g.batchingIndex.isLt.le bits inputs hpublic nd bd hprime hbinary w
      (selected _ hc (by dsimp only [ApplicationPrefix.conversionIndex,ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart]; omega)) hbad
    refine ⟨ApplicationPrefix.conversionIndex g,hc,?_⟩
    rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.conversion_single binary prime P R cfg S laws e cfg.initialLink output.proof H readers]
    exact indicator_charged hlocal

variable [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]

/-- Actual decoding supplies all late data and the selected pair. Each
failure is then charged at its real earlier boundary, including selection
collisions at the first fingerprint query. -/
theorem decoded_failure_cover
    (hlayout : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
    (primeGeometry : primePlan.frontend = g.prime)
    (binaryGeometry : binaryTemplate.frontend = g.binary)
    (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
    (output : Output) (H : Point → Digest × C) (decoded : Decoded)
    (hd : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H = some decoded)
    (hfailure : ¬ ∃ w,
      (RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded).context.extract = some w ∧
        decoded.application.True w) :
    RuntimeAdaptiveBackend.Bad binary prime P R cfg earlier cutOracle cutoff output H decoded ∨
      Charged binary prime P R cfg earlier hashPublic decodePublic layout cutoff cutOracle cutOff laws
        primePlan primeFits binaryTemplate binaryFits output H := by
  let e := encodings output.request
  let auth := RuntimeAdaptiveBackend.authentication binary prime P R cfg earlier cutOracle cutoff output H decoded
  have hs := (RuntimeAdaptiveVerifier.decode_spec binary prime P R cfg earlier hashPublic decodePublic draw output H decoded hd).1
  rw [BackendPath.parent_point] at hs
  rcases auth.extraction_failure_cover hfailure with hbackend | ⟨w,hselected,hbad⟩
  · rcases (RuntimeAdaptiveBackend.bad_or_collision binary prime P R cfg earlier cutOracle cutoff output H decoded).mp hbackend
      with hbad | hcollision
    · exact Or.inl hbad
    · have hc := RuntimeAdaptiveStatement.collision_on_replay binary prime P R cfg hashPublic decodePublic layout hlayout cutoff cutOracle cutOff
        e cfg.initialLink output.proof H g.batchingIndex.val g.batchingIndex.isLt.le
        (by simp only [Geometry.batchingIndex_val,Geometry.backendPrefix,List.length_append,List.length_cons,List.length_nil]; omega)
        ⟨decoded.application,decoded.statement⟩ hs decoded.coin (RuntimeVerifier.responses binary prime P R cfg output.proof) hcollision
      refine Or.inr ⟨0,by rw [g.roles_length]; omega,?_⟩
      rw [RuntimeAdaptiveVerifier.point_eq,RuntimeAdaptiveRoles.fingerprint_single binary prime P R cfg S laws e cfg.initialLink output.proof H readers]
      rcases hc with hb | hp
      · have hn : 0 ≤ indicator ((S).primeSelection ((e.chain cfg.initialLink).point output.proof H 0) H
            (H ((e.chain cfg.initialLink).point output.proof H 0)).2) := by
          unfold indicator; split_ifs <;> norm_num
        simpa only [e,indicator,if_pos hb,le_add_iff_nonneg_right] using hn
      · have hn : 0 ≤ indicator ((S).binarySelection ((e.chain cfg.initialLink).point output.proof H 0) H
            (H ((e.chain cfg.initialLink).point output.proof H 0)).2) := by
          unfold indicator; split_ifs <;> norm_num
        simpa only [e,indicator,if_pos hp,le_add_iff_nonneg_left] using hn
  · have hA := (RuntimeAdaptiveStatement.statementAt_spec binary prime P R cfg hashPublic decodePublic _ _ _ hs).1
    obtain ⟨bits,inputs,hbits,hinputs,happlication⟩ :=
      RuntimeAdaptive.application_spec binary prime P R cfg hashPublic decodePublic _ _ _ hA
    obtain ⟨nd,bd,hprime,hbinary,hsetup⟩ := ApplicationPrefix.decodeChecked_spec (binaryWithBits binary bits)
      (primeWithInputs prime inputs) cfg.card cfg.polynomialX cfg.quotientBound cfg.packingDegree cfg.binaryField cfg.primeField
      cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback _ _ _ happlication
    have hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
        ((e.chain cfg.initialLink).point output.proof H g.batchingIndex.val) = some (bits,inputs) := by
      dsimp only [e]
      simp only [RuntimeAdaptiveViews.publics,Option.bind_eq_bind,hbits,hinputs,Option.bind_some]
    exact Or.inr (parsed_charged binary prime P R cfg earlier hashPublic decodePublic layout cutoff cutOracle cutOff laws
      primePlan primeFits binaryTemplate binaryFits hlayout primeGeometry binaryGeometry output H decoded hs bits inputs hpublic
      nd bd hprime hbinary w hselected ((parsedBad_iff binary prime P R cfg bits inputs nd bd decoded.application hsetup w).mp hbad))

end LfzkV2.Current.RuntimeAdaptiveAccepted
