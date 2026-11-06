import LfzkV2.Current.RuntimeAdaptiveReplay

/-! Conversion and packing events at their actual adaptive query boundaries.
Only public values already recovered from those prefixes enter the local tests. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveAuxiliary
open Application ApplicationSetup ApplicationViews ApplicationOracle RuntimeAdaptive RecursivePolygero SumcheckV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable {binary : BinaryPublic B shared maskBits adviceBits} {prime : PrimePublic N shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable {S : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) binary prime (Oracle := Oracle)}
variable (laws : RuntimeCover.SamplerLaws binary prime P R cfg S)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (primeGeometry : primePlan.frontend = g.prime)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "Output" => RuntimeVerifier.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Generator" => cfg.generator^Adapter.Mdoc.generatorExponent
variable (e : Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (initialLink : Digest)
variable (proof : Replay.Output g fields Advice (RuntimeVerifier.Authentication (g := g)))
variable (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) → Digest × C)

include primePlan primeGeometry in
private theorem prime_window : g.primeStart+FrontendReplay.slots prime.circuit =
    ApplicationPrefix.rowBatchingIndex g := by
  rw [primePlan.slots_eq_roles_length .prime,primeGeometry]
  rfl

omit [Fintype C] in
/-- Successful strict-past parsing identifies both the earlier rank and
its actual answer; no late tape value is supplied to the local test. -/
private theorem strictAnswer_from_late (proof : Output) (H : Point → Digest × C)
    (later : ℕ) (hlater : later ≤ g.roles.length) (index : ℕ) (answer : C)
    (hanswer : ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H later)
      (((e.chain initialLink).point proof H later).priorAnswers H) index = some answer) :
    index < later ∧ answer = (H ((e.chain initialLink).point proof H index)).2 := by
  have hr := (e.chain initialLink).point_rank proof H hlater
  change Input.rank _ = later at hr
  have hpast : index < later := by
    by_contra h
    have hnone : ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H later)
        (((e.chain initialLink).point proof H later).priorAnswers H) index = none := by
      unfold ApplicationPrefix.strictAnswer
      rw [dif_neg (by rw [hr]; omega)]
    rw [hnone] at hanswer
    contradiction
  refine ⟨hpast,?_⟩
  have he := ApplicationViewReplay.strictAnswer_replay e initialLink proof H later index hlater hpast
  exact Option.some.inj (hanswer.symm.trans he)

include primePlan primeGeometry in
/-- Both conversion coordinates are taken from the same actual answer.
The already-bound target is recovered from that boundary's prover block. -/
theorem conversion_of_late
    (later : ℕ) (hlater : later ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H later) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hread : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H later)
      (((e.chain initialLink).point proof H later).priorAnswers H) = some nd)
    (hbinary : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree
      cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero
      cfg.conversion cfg.advice cfg.fallback ((e.chain initialLink).point proof H later)
      (((e.chain initialLink).point proof H later).priorAnswers H) = some bd)
    (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H
      (ApplicationPrefix.conversionIndex g)) H = some w)
    (hbad : Handoff.ConversionBad nd.claim.sharedWeights bd.eta bd.mu
      ((binaryWithBits binary bits).sharedValues w.1) ((binaryWithBits binary bits).mask w.1) Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound bd.alpha) :
    conversionBad S (RuntimeAdaptiveViews.readConversion binary prime P R cfg hashPublic decodePublic) laws.conversionDecoder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound ((e.chain initialLink).point proof H
        (ApplicationPrefix.conversionIndex g)) H
      (H ((e.chain initialLink).point proof H (ApplicationPrefix.conversionIndex g))).2 := by
  let index := ApplicationPrefix.conversionIndex g
  let point := (e.chain initialLink).point proof H index
  have hindex : index < g.roles.length := by
    have hh := g.roles_length
    simp only [index,ApplicationPrefix.conversionIndex,ApplicationPrefix.rowBatchingIndex,
      Geometry.primeStart] at *
    omega
  have hs := ApplicationPrefix.readPrime_spec (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
    cfg.primeNonzero cfg.fallback _ _ nd hread
  have hb := ApplicationPrefix.readBinary_spec (binaryWithBits binary bits) nd Generator cfg.packingDegree
    cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero
    cfg.conversion cfg.advice cfg.fallback _ _ bd hbinary
  have hr := (e.chain initialLink).point_rank proof H hlater
  change Input.rank _ = later at hr
  obtain ⟨answer,hanswer,halpha⟩ := hb.2.2.1
  obtain ⟨hpast,ha⟩ := strictAnswer_from_late e initialLink proof H later hlater index answer hanswer
  have hprime := ApplicationViewReplay.readPrime_from_late e initialLink proof (primeWithInputs prime inputs)
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback H index later hindex.le hlater
    (by change g.primeStart+FrontendReplay.slots prime.circuit ≤ index
        rw [prime_window primePlan primeGeometry]; dsimp [index,ApplicationPrefix.conversionIndex]; omega)
    (by have hh := hs.1
        change g.primeStart+FrontendReplay.slots prime.circuit ≤ ((e.chain initialLink).point proof H later).rank at hh
        rw [hr] at hh
        exact hh)
    (by dsimp [index,ApplicationPrefix.conversionIndex]; omega)
    (by dsimp [index,ApplicationPrefix.conversionIndex] at hpast; omega) nd hread
  obtain ⟨scale,hscale,heta⟩ := hb.2.1
  have hscaleEarly : ApplicationPrefix.strictAnswer point (point.priorAnswers H)
      (ApplicationPrefix.rescalingIndex g) = some scale := by
    rw [ApplicationViewReplay.strictAnswer_replay_eq e initialLink proof H index later
      (ApplicationPrefix.rescalingIndex g) hindex.le hlater
      (by dsimp [index,ApplicationPrefix.rescalingIndex,ApplicationPrefix.conversionIndex]; omega)
      (by dsimp [index,ApplicationPrefix.rescalingIndex,ApplicationPrefix.conversionIndex] at hpast ⊢; omega)]
    exact hscale
  have hmu : point.readAt index (fun block => block.2.mu.map cfg.primeField) = some bd.mu := by
    rw [ApplicationViewReplay.readAt_replay_eq e initialLink proof H
      (fun block => block.2.mu.map cfg.primeField) index later index hindex.le hlater hindex le_rfl hpast.le]
    exact hb.2.2.2.1
  refine ⟨w,hselected,?_⟩
  change optionBad (fun packet w answer => packet.bad Adapter.Mdoc.groupOrder
    Adapter.Mdoc.quotientBound w (laws.conversionDecoder.decode answer))
    ((RuntimeAdaptiveViews.readConversion binary prime P R cfg hashPublic decodePublic) point (point.priorAnswers H)) w (H point).2
  unfold RuntimeAdaptiveViews.readConversion
  have hstart : g.primeStart ≤ index := by
    dsimp only [index,ApplicationPrefix.conversionIndex,ApplicationPrefix.rescalingIndex,
      ApplicationPrefix.rowBatchingIndex]; omega
  have hpublicEarly := (RuntimeAdaptiveReplay.publics_replay_eq binary prime hashPublic decodePublic
    e initialLink proof H index later hindex.le hlater (lt_of_le_of_lt hstart hindex)
    hstart (hstart.trans hpast.le)).trans hpublic
  rw [hpublicEarly]
  simp only [Option.bind_eq_bind,Option.bind_some]
  unfold readConversionPacket
  rw [hprime,hscaleEarly,hmu]
  change ConversionData.bad _ Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound w
    (laws.conversionDecoder.decode (H point).2)
  rw [laws.conversion_agrees]
  unfold ConversionData.bad
  rw [← heta]
  rw [halpha,ha] at hbad
  exact ⟨hbad.1,hbad.2 0,hbad.2 1⟩

variable (binaryTemplate : FrontendSchedule.Plan B binary.template)
variable (binaryGeometry : binaryTemplate.frontend = g.binary)

include primePlan primeGeometry binaryTemplate binaryGeometry in
/-- The packing equation is tested before its challenge, after public values
and its completed binary source are fixed by the actual prefix. -/
theorem packing_of_late
    (later : ℕ) (hlater : later ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H later) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hreadPrime : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H later)
      (((e.chain initialLink).point proof H later).priorAnswers H) = some nd)
    (hreadBinary : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree
      cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero
      cfg.conversion cfg.advice cfg.fallback ((e.chain initialLink).point proof H later)
      (((e.chain initialLink).point proof H later).priorAnswers H) = some bd)
    (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H
      (ApplicationPrefix.packingIndex g)) H = some w)
    (hbad : bd.frontend.source.Bad (binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w) bd.U bd.delta) :
    packingBad S (RuntimeAdaptiveViews.readPacking binary prime P R cfg hashPublic decodePublic) laws.packingDecoder
      ((e.chain initialLink).point proof H (ApplicationPrefix.packingIndex g)) H
      (H ((e.chain initialLink).point proof H (ApplicationPrefix.packingIndex g))).2 := by
  let index := ApplicationPrefix.packingIndex g
  let point := (e.chain initialLink).point proof H index
  have hindex : index < g.roles.length := by
    have hlength := g.roles_length
    simp only [index,ApplicationPrefix.packingIndex,Geometry.binaryStart] at *
    omega
  have hr := (e.chain initialLink).point_rank proof H hlater
  change Input.rank _ = later at hr
  have hn := ApplicationPrefix.readPrime_spec (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
    cfg.primeNonzero cfg.fallback _ _ nd hreadPrime
  have hprimeWindow : g.primeStart+FrontendReplay.slots prime.circuit =
      ApplicationPrefix.rowBatchingIndex g := by
    rw [primePlan.slots_eq_roles_length .prime,primeGeometry]
    rfl
  have hwindowLate : g.primeStart+FrontendReplay.slots prime.circuit ≤ later := by
    have hh := hn.1
    change g.primeStart+FrontendReplay.slots prime.circuit ≤ ((e.chain initialLink).point proof H later).rank at hh
    rw [hr] at hh
    exact hh
  have hs := ApplicationPrefix.readBinary_spec (binaryWithBits binary bits) nd Generator cfg.packingDegree cfg.binaryField
    cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice
    cfg.fallback _ _ bd hreadBinary
  obtain ⟨_,_,_,_,_,⟨U,hU,hUeq⟩,⟨packing,hpacking,hdelta⟩,_,_,hdecode,hnonzero,_⟩ := hs
  have hpast : index < later := by
    by_contra h
    have hnone : ApplicationPrefix.strictAnswer
        ((e.chain initialLink).point proof H later)
        (((e.chain initialLink).point proof H later).priorAnswers H) index = none := by
      unfold ApplicationPrefix.strictAnswer
      rw [dif_neg (by rw [hr]; omega)]
    rw [hnone] at hpacking
    contradiction
  let adapter : AdapterPacket (binaryWithBits binary bits) (primeWithInputs prime inputs) C := ⟨nd,bd.eta,bd.mu,bd.alpha,bd.masked⟩
  have hbinarySlots : FrontendReplay.slots bd.setup.circuit = (g.binary.roles .binary).length := by
    have h := (RuntimeShape.binaryPlan (binaryWithBits binary bits) (primeWithInputs prime inputs)
      Generator binaryTemplate adapter).slots_eq_roles_length .binary
    rw [RuntimeShape.binaryPlan_frontend] at h
    change FrontendReplay.slots bd.setup.circuit = (binaryTemplate.frontend.roles .binary).length at h
    rw [binaryGeometry] at h
    exact h
  have hwindow : g.binaryStart+FrontendReplay.slots bd.setup.circuit ≤ index := by
    rw [hbinarySlots]
    rfl
  have hprimeEarlier : g.primeStart+FrontendReplay.slots prime.circuit ≤ index := by
    rw [hprimeWindow]
    simp only [index,ApplicationPrefix.packingIndex,ApplicationPrefix.rowBatchingIndex,
      Geometry.primeStart,Geometry.binaryStart]
    omega
  have hconversion : ApplicationPrefix.conversionIndex g < index := by
    simp only [index,ApplicationPrefix.packingIndex,ApplicationPrefix.conversionIndex,
      ApplicationPrefix.rowBatchingIndex,Geometry.primeStart,Geometry.binaryStart]
    omega
  have hstart : g.binaryStart ≤ index := by unfold index ApplicationPrefix.packingIndex; omega
  have hpacket := ApplicationViewReplay.readBinaryPacket_from_late e initialLink proof (binaryWithBits binary bits) (primeWithInputs prime inputs)
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback H index later
    hindex.le hlater hprimeEarlier hwindowLate hconversion (lt_trans hconversion hpast) hstart
    (hstart.trans hpast.le) nd Generator cfg.packingDegree cfg.binaryField cfg.binaryDecode
    cfg.binaryNonzero bd hwindow hreadPrime hreadBinary
  have hreadU : point.readAt index (fun block => block.2.packingU) = some U :=
    (ApplicationViewReplay.readAt_replay_eq e initialLink proof H (fun block => block.2.packingU)
      index later index hindex.le hlater hindex le_rfl hpast.le).trans hU
  have hpacketPacking := ApplicationViewReplay.readPackingPacket_of_readBinaryPacket (binaryWithBits binary bits) (primeWithInputs prime inputs)
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
    nd Generator cfg.packingDegree cfg.binaryField cfg.binaryDecode cfg.binaryNonzero bd
    point (point.priorAnswers H) hpacket hdecode hnonzero U hreadU hUeq
  have hanswer : packing = (H point).2 :=
    Option.some.inj (hpacking.symm.trans
      (ApplicationViewReplay.strictAnswer_replay e initialLink proof H later index hlater hpast))
  have hdeltaCurrent : bd.delta = laws.packingDecoder.decode (H point).2 := by
    funext i
    rw [hdelta,laws.packing_agrees,hanswer]
  refine ⟨w,hselected,?_⟩
  have hstartPrime : g.primeStart ≤ index := by
    dsimp only [index,ApplicationPrefix.packingIndex,Geometry.primeStart,Geometry.binaryStart]; omega
  have hpublicEarly := (RuntimeAdaptiveReplay.publics_replay_eq binary prime hashPublic decodePublic
    e initialLink proof H index later hindex.le hlater (lt_of_le_of_lt hstartPrime hindex)
    hstartPrime (hstartPrime.trans hpast.le)).trans hpublic
  change optionBad (fun packet w answer => packet.bad w (laws.packingDecoder.decode answer))
    ((RuntimeAdaptiveViews.readPacking binary prime P R cfg hashPublic decodePublic) point (point.priorAnswers H)) w (H point).2
  unfold RuntimeAdaptiveViews.readPacking
  rw [hpublicEarly]
  simp only [Option.bind_eq_bind,Option.bind_some]
  change optionBad _ (readPackingPacket (binaryWithBits binary bits) (primeWithInputs prime inputs) Generator cfg.packingDegree cfg.binaryField
    cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeDecode cfg.primeNonzero
    cfg.conversion cfg.advice cfg.fallback point (point.priorAnswers H)) w (H point).2
  rw [hpacketPacking]
  change bd.frontend.source.Bad (binaryValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w) bd.U (laws.packingDecoder.decode (H point).2)
  rw [← hdeltaCurrent]
  exact hbad

end LfzkV2.Current.RuntimeAdaptiveAuxiliary
