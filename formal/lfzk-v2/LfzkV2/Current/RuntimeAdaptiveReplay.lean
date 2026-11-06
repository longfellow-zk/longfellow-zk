import LfzkV2.Current.RuntimeAdaptiveViews
import LfzkV2.Current.ApplicationViewFrontend

/-! Successful late adaptive parsing reconstructs each earlier local frontend
view. Public values are recovered from the same bound prefix, and unavailable
future prover messages are completed only by the existing partial parser. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveReplay
open Application ApplicationSetup ApplicationViews ApplicationOracle RuntimeAdaptive RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt))
variable (S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle))
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg S)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent
variable (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (initialLink : Digest)
variable (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
variable (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C)

omit [Fintype B] [DecidableEq B] [Fintype C] in
/-- Different public prime values may share the first fingerprint prefix.
Once their prime-start block is bound, every later prefix reads one value. -/
theorem publics_replay_eq (n m : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hstart : g.primeStart < g.roles.length) (hpn : g.primeStart ≤ n) (hpm : g.primeStart ≤ m) :
    RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic ((e.chain initialLink).point proof H n) =
      RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic ((e.chain initialLink).point proof H m) := by
  unfold RuntimeAdaptiveViews.publics
  rw [e.point_context initialLink proof H n,e.point_context initialLink proof H m,
    RuntimeAdaptive.primePublic_replay_eq prime decodePublic e initialLink proof H n m hn hm hstart hpn hpm]

theorem primeRead_from_late
    (n m : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hpn : g.primeStart ≤ n) (hnm : n < m)
    (hfit : g.primeStart+FrontendReplay.slots prime.circuit ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (data : PrimeData (primeWithInputs prime inputs) C)
    (hlate : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some data) :
    ∃ early,
      RuntimeAdaptiveViews.readPrimeView binary prime P R cfg S laws hashPublic decodePublic primePlan primeFits
          ((e.chain initialLink).point proof H n) (((e.chain initialLink).point proof H n).priorAnswers H) =
        some (primeViewOfPayload (binaryWithBits binary bits) (primeWithInputs prime inputs)
          primePlan laws.primeCapacity cfg.primeDecode cfg.primeNonzero laws.primeDecoder primeFits cfg.fallback early) ∧
      ∀ role, FrontendReplay.queryIndex prime.circuit role 0 ≤ n-g.primeStart →
        Layered.Replay.layerMessage prime.circuit early role =
          Layered.Replay.layerMessage prime.circuit data.payload role := by
  have hs := ApplicationPrefix.readPrime_spec (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
    cfg.primeNonzero cfg.fallback _ _ data hlate
  have hstart : g.primeStart < g.roles.length := by omega
  have hearly := (publics_replay_eq binary prime hashPublic decodePublic e initialLink proof H
    n m hn hm hstart hpn (by omega)).trans hpublic
  obtain ⟨early,hread,hmessages⟩ := ApplicationViews.primeView_from_late e (binaryWithBits binary bits)
    (primeWithInputs prime inputs) primePlan laws.primeCapacity cfg.primeDecode cfg.primeNonzero
    laws.primeDecoder primeFits cfg.primeField cfg.fallback initialLink proof H n m hn hm hpn
    hnm.le hfit data.payload hs.2.1
  refine ⟨early,?_,hmessages⟩
  unfold RuntimeAdaptiveViews.readPrimeView
  rw [hearly]
  exact hread

theorem binaryRead_from_late
    (primeGeometry : primePlan.frontend = g.prime)
    (n m : ℕ) (hn : n ≤ g.roles.length) (hm : m ≤ g.roles.length)
    (hpn : g.binaryStart ≤ n) (hnm : n < m)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hprime : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some nd)
    (hbinary : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree
      cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion
      cfg.advice cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some bd) :
    let currentBinary := binaryWithBits binary bits
    let currentPrime := primeWithInputs prime inputs
    let packet : AdapterPacket currentBinary currentPrime C := ⟨nd,bd.eta,bd.mu,bd.alpha,bd.masked⟩
    ∃ early,
      RuntimeAdaptiveViews.readBinaryView binary prime P R cfg S laws hashPublic decodePublic binaryTemplate binaryFits
          ((e.chain initialLink).point proof H n) (((e.chain initialLink).point proof H n).priorAnswers H) =
        some (binaryViewOfPayload currentBinary currentPrime Generator packet
          (RuntimeShape.binaryPlan currentBinary currentPrime Generator binaryTemplate packet)
          laws.binaryCapacity cfg.binaryDecode cfg.binaryNonzero laws.binaryDecoder
          (by rw [RuntimeShape.binaryPlan_capacity]; exact binaryFits) cfg.fallback early) ∧
      ∀ role, FrontendReplay.queryIndex bd.setup.circuit role 0 ≤ n-g.binaryStart →
        Layered.Replay.layerMessage bd.setup.circuit early role =
          Layered.Replay.layerMessage bd.setup.circuit bd.payload role := by
  let currentBinary := binaryWithBits binary bits
  let currentPrime := primeWithInputs prime inputs
  let packet : AdapterPacket currentBinary currentPrime C := ⟨nd,bd.eta,bd.mu,bd.alpha,bd.masked⟩
  have hs := ApplicationPrefix.readBinary_spec currentBinary nd Generator cfg.packingDegree cfg.binaryField
    cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice
    cfg.fallback _ _ bd hbinary
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  have hfit : g.binaryStart+FrontendReplay.slots bd.setup.circuit ≤ g.roles.length := by
    have hw : g.binaryStart+FrontendReplay.slots bd.setup.circuit ≤ m := by simpa only [hr] using hs.1
    omega
  have hprimeWindow : g.primeStart+FrontendReplay.slots prime.circuit ≤ n := by
    rw [primePlan.slots_eq_roles_length .prime,primeGeometry]
    dsimp only [Geometry.primeStart,Geometry.binaryStart] at *
    omega
  have hconversion : ApplicationPrefix.conversionIndex g < n := by
    dsimp only [ApplicationPrefix.conversionIndex,ApplicationPrefix.rescalingIndex,
      ApplicationPrefix.rowBatchingIndex,Geometry.primeStart,Geometry.binaryStart] at *
    omega
  have hpublicStart : g.primeStart ≤ n := by
    dsimp only [Geometry.primeStart,Geometry.binaryStart] at *
    omega
  have hstart : g.primeStart < g.roles.length := by omega
  have hpubEarly := (publics_replay_eq binary prime hashPublic decodePublic e initialLink proof H
    n m hn hm hstart hpublicStart (by omega)).trans hpublic
  have hadapter := ApplicationViewReplay.readAdapter_from_late e initialLink proof currentBinary currentPrime
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback H n m hn hm
    hprimeWindow (by change g.primeStart+FrontendReplay.slots prime.circuit ≤ m; omega) hconversion (by omega) hpn (by omega) nd Generator cfg.packingDegree
    cfg.binaryField cfg.binaryDecode cfg.binaryNonzero bd hprime hbinary
  obtain ⟨early,hread,hmessages⟩ := ApplicationViews.binaryView_from_late e currentBinary currentPrime
    Generator laws.binaryCapacity (RuntimeShape.binaryPlan currentBinary currentPrime Generator binaryTemplate)
    cfg.binaryDecode cfg.binaryNonzero laws.binaryDecoder
    (fun packet => by rw [RuntimeShape.binaryPlan_capacity]; exact binaryFits)
    cfg.binaryField cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
    initialLink proof H n m hn hm hpn hnm.le packet hadapter hfit bd.payload hs.2.2.2.2.2.2.2.2.1
  refine ⟨early,?_,hmessages⟩
  unfold RuntimeAdaptiveViews.readBinaryView
  rw [hpubEarly]
  exact hread

end LfzkV2.Current.RuntimeAdaptiveReplay
