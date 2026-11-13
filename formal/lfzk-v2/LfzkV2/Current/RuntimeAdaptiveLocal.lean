import LfzkV2.Current.RuntimeAdaptiveReplay

/-! Actual local frontend errors with adaptively bound public values. Earlier
view success and all answer/message consistency are derived from late parsing. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveLocal
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
variable (S : RuntimeSource.Source (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle))
variable (laws : RuntimeSource.SamplerLaws binary prime P R cfg S)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeFits : primePlan.capacity ≤ laws.primeCapacity)
variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryFits : binaryTemplate.capacity ≤ laws.binaryCapacity)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Generator" => cfg.polynomialX^Adapter.Mdoc.generatorExponent
variable (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (initialLink : Digest)
variable (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
variable (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C)

local notation "Pair" => Selection.Pair B N binary.Original prime.Original

theorem prime_bad
    (m : ℕ) (hm : m ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (hread : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some nd)
    (query : ℕ) (hquery : query < FrontendReplay.slots prime.circuit) (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H (g.primeStart+query)) H = some w)
    (hbad : FrontendReplay.BadAt nd.decode nd.nonzero prime.circuit prime.setup.plan nd.payload nd.answers
      (primeInputs (binaryWithBits binary bits) (primeWithInputs prime inputs) w)
      (fun i => primeFullValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w
        (.inr (CellLayout.Prime.pad prime.remaining prime.pads i))) query) :
    frontendBad S (RuntimeAdaptiveViews.readPrimeView binary prime P R cfg S laws hashPublic decodePublic primePlan primeFits)
      ((e.chain initialLink).point proof H (g.primeStart+query)) H
      (H ((e.chain initialLink).point proof H (g.primeStart+query))).2 := by
  let current := g.primeStart+query
  let currentBinary := binaryWithBits binary bits
  let currentPrime := primeWithInputs prime inputs
  have hs := ApplicationPrefix.readPrime_spec currentPrime cfg.primeField cfg.primeDecode cfg.primeNonzero
    cfg.fallback _ _ nd hread
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  have hwindow := hs.1
  change g.primeStart+FrontendReplay.slots prime.circuit ≤
    ((e.chain initialLink).point proof H m).rank at hwindow
  rw [hr] at hwindow
  have hcm : current < m := by dsimp only [current]; omega
  have hc : current ≤ g.roles.length := by omega
  have hstart : g.primeStart ≤ current := by dsimp only [current]; omega
  have hfit : g.primeStart+FrontendReplay.slots prime.circuit ≤ g.roles.length := by omega
  obtain ⟨early,hearly,hmessages⟩ := RuntimeAdaptiveReplay.primeRead_from_late binary prime P R cfg S laws
    hashPublic decodePublic primePlan primeFits e initialLink proof H current m hc hm hstart hcm hfit
    bits inputs hpublic nd hread
  let view : FrontendView N (Fin prime.pads) Pair Point C := primeViewOfPayload currentBinary currentPrime
    primePlan laws.primeCapacity cfg.primeDecode cfg.primeNonzero laws.primeDecoder primeFits cfg.fallback early
  have hcurrent := (e.chain initialLink).point_rank proof H hc
  change Input.rank _ = current at hcurrent
  have hindex : ((e.chain initialLink).point proof H current).rank-g.primeStart = query := by
    rw [hcurrent]; dsimp only [current]; omega
  apply frontendBad_of_prefix S _ _ H _ view hearly w nd.payload nd.answers
  · change g.primeStart ≤ _; rwa [hcurrent]
  · exact hselected
  · intro j hj
    change j ≤ ((e.chain initialLink).point proof H current).rank-g.primeStart at hj
    rw [hcurrent] at hj
    rw [hs.2.2.2.2.1]
    exact frontendTape_eq_answersWith e initialLink proof H current m g.primeStart
      (FrontendReplay.slots prime.circuit) hc hm hstart hcm (by dsimp only [current]; omega) cfg.fallback j hj
  · intro role hrole
    change FrontendReplay.queryIndex prime.circuit role 0 ≤
      ((e.chain initialLink).point proof H current).rank-g.primeStart at hrole
    rw [hcurrent] at hrole
    exact (hmessages role hrole).symm
  · change FrontendReplay.BadAt cfg.primeDecode cfg.primeNonzero prime.circuit prime.setup.plan
      nd.payload nd.answers (primeInputs currentBinary currentPrime w)
      (fun i => primeFullValues currentBinary currentPrime w
        (.inr (CellLayout.Prime.pad prime.remaining prime.pads i)))
      (((e.chain initialLink).point proof H current).rank-g.primeStart)
    rw [hindex]
    simpa only [hs.2.2.1,hs.2.2.2.1] using hbad

theorem binary_bad
    (primeGeometry : primePlan.frontend = g.prime)
    (m : ℕ) (hm : m ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hprime : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some nd)
    (hread : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree
      cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion
      cfg.advice cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some bd)
    (query : ℕ) (hquery : query < FrontendReplay.slots bd.setup.circuit) (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H (g.binaryStart+query)) H = some w)
    (hbad : FrontendReplay.BadAt bd.decode bd.nonzero bd.setup.circuit bd.setup.plan bd.payload bd.answers
      ((binaryWithBits binary bits).inputs (binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w))
      (fun i => binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w
        (CellLayout.Binary.pad binary.words binary.degree binary.pads i)) query) :
    frontendBad S (RuntimeAdaptiveViews.readBinaryView binary prime P R cfg S laws hashPublic decodePublic binaryTemplate binaryFits)
      ((e.chain initialLink).point proof H (g.binaryStart+query)) H
      (H ((e.chain initialLink).point proof H (g.binaryStart+query))).2 := by
  let current := g.binaryStart+query
  let currentBinary := binaryWithBits binary bits
  let currentPrime := primeWithInputs prime inputs
  let packet : AdapterPacket currentBinary currentPrime C := ⟨nd,bd.eta,bd.mu,bd.alpha,bd.masked⟩
  have hs := ApplicationPrefix.readBinary_spec currentBinary nd Generator cfg.packingDegree cfg.binaryField
    cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
    _ _ bd hread
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  have hwindow : g.binaryStart+FrontendReplay.slots bd.setup.circuit ≤ m := by simpa only [hr] using hs.1
  have hcm : current < m := by dsimp only [current]; omega
  have hc : current ≤ g.roles.length := by omega
  have hstart : g.binaryStart ≤ current := by dsimp only [current]; omega
  obtain ⟨early,hearly,hmessages⟩ := RuntimeAdaptiveReplay.binaryRead_from_late binary prime P R cfg S laws
    hashPublic decodePublic primePlan binaryTemplate binaryFits e initialLink proof H primeGeometry
    current m hc hm hstart hcm bits inputs hpublic nd bd hprime hread
  let view : FrontendView B binary.Pad Pair Point C := binaryViewOfPayload currentBinary currentPrime Generator packet
    (RuntimeShape.binaryPlan currentBinary currentPrime Generator binaryTemplate packet)
    laws.binaryCapacity cfg.binaryDecode cfg.binaryNonzero laws.binaryDecoder
    (by rw [RuntimeShape.binaryPlan_capacity]; exact binaryFits) cfg.fallback early
  have hcurrent := (e.chain initialLink).point_rank proof H hc
  change Input.rank _ = current at hcurrent
  have hindex : ((e.chain initialLink).point proof H current).rank-g.binaryStart = query := by
    rw [hcurrent]; dsimp only [current]; omega
  apply frontendBad_of_prefix S _ _ H _ view hearly w bd.payload bd.answers
  · change g.binaryStart ≤ _; rwa [hcurrent]
  · exact hselected
  · intro j hj
    change j ≤ ((e.chain initialLink).point proof H current).rank-g.binaryStart at hj
    rw [hcurrent] at hj
    rw [hs.2.2.2.2.2.2.2.2.2.2.2]
    exact frontendTape_eq_answersWith e initialLink proof H current m g.binaryStart
      (FrontendReplay.slots bd.setup.circuit) hc hm hstart hcm (by dsimp only [current]; omega) cfg.fallback j hj
  · intro role hrole
    change FrontendReplay.queryIndex bd.setup.circuit role 0 ≤
      ((e.chain initialLink).point proof H current).rank-g.binaryStart at hrole
    rw [hcurrent] at hrole
    exact (hmessages role hrole).symm
  · change FrontendReplay.BadAt cfg.binaryDecode cfg.binaryNonzero bd.setup.circuit bd.setup.plan
      bd.payload bd.answers (currentBinary.inputs (binaryValues currentBinary currentPrime w))
      (fun i => binaryValues currentBinary currentPrime w (CellLayout.Binary.pad binary.words binary.degree binary.pads i))
      (((e.chain initialLink).point proof H current).rank-g.binaryStart)
    rw [hindex]
    simpa only [hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1] using hbad

end LfzkV2.Current.RuntimeAdaptiveLocal
