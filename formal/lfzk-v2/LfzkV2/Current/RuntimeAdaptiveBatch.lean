import LfzkV2.Current.RuntimeAdaptiveReplay

/-! Adaptive prime-field row batching and rescaling. Public vectors and
packets are recovered from their actual binding positions before testing
the explicit current challenge. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveBatch
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

include primePlan in
private theorem prime_window (geometry : primePlan.frontend = g.prime) :
    g.primeStart+FrontendReplay.slots prime.circuit = ApplicationPrefix.rowBatchingIndex g := by
  rw [primePlan.slots_eq_roles_length .prime,geometry]
  rfl

private theorem transported_decode {F : Type} [Fintype F] {a b : ℕ} (h : a = b)
    (decoder : BalancedDecoder C (Fin b → F)) (answer : C) (i : Fin a) :
    (h.symm ▸ decoder).decode answer i = decoder.decode answer (Fin.cast h i) := by
  cases h
  rfl

omit [Fintype C] in
private theorem strictAnswer_from_late (m : ℕ) (hm : m ≤ g.roles.length) (index : ℕ) (answer : C)
    (hanswer : ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) index = some answer) :
    index < m ∧ answer = (H ((e.chain initialLink).point proof H index)).2 := by
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  have hpast : index < m := by
    by_contra h
    have hnone : ApplicationPrefix.strictAnswer ((e.chain initialLink).point proof H m)
        (((e.chain initialLink).point proof H m).priorAnswers H) index = none := by
      unfold ApplicationPrefix.strictAnswer
      rw [dif_neg (by rw [hr]; omega)]
    rw [hnone] at hanswer
    contradiction
  refine ⟨hpast,?_⟩
  have he := ApplicationViewReplay.strictAnswer_replay e initialLink proof H m index hm hpast
  exact Option.some.inj (hanswer.symm.trans he)

theorem batch_of_late
    (primeGeometry : primePlan.frontend = g.prime)
    (m : ℕ) (hm : m ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (hread : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some nd)
    (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g)) H = some w)
    (hbad : Prime.BatchBad (fun i => (nd.frontend.rows.get i).eval
      (primeFullValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w)) nd.rho) :
    batchBad S (RuntimeAdaptiveViews.readBatch binary prime P R cfg S laws hashPublic decodePublic)
      ((e.chain initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g)) H
      (H ((e.chain initialLink).point proof H (ApplicationPrefix.rowBatchingIndex g))).2 := by
  let index := ApplicationPrefix.rowBatchingIndex g
  let point := (e.chain initialLink).point proof H index
  let currentBinary := binaryWithBits binary bits
  let currentPrime := primeWithInputs prime inputs
  have hindex : index < g.roles.length := by
    have hh := g.roles_length
    simp only [index,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *
    omega
  have hs := ApplicationPrefix.readPrime_spec currentPrime cfg.primeField cfg.primeDecode cfg.primeNonzero
    cfg.fallback _ _ nd hread
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  have hwindow := hs.1
  change g.primeStart+FrontendReplay.slots prime.circuit ≤
    ((e.chain initialLink).point proof H m).rank at hwindow
  rw [hr] at hwindow
  have hw : g.primeStart+FrontendReplay.slots prime.circuit = index := prime_window prime primePlan primeGeometry
  have hpacket := ApplicationViewReplay.readPrimePacket_from_late e initialLink proof currentPrime
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback H index m hindex.le hm
    hw.le hwindow nd hread
  obtain ⟨answer,hanswer,hrho⟩ := hs.2.2.2.2.2
  obtain ⟨hpast,ha⟩ := strictAnswer_from_late e initialLink proof H m hm index answer hanswer
  have hpubEarly := (RuntimeAdaptiveReplay.publics_replay_eq binary prime hashPublic decodePublic e initialLink proof H
    index m hindex.le hm (by
      have hh := g.roles_length
      dsimp only [Geometry.primeStart] at *
      omega) (by dsimp only [index,ApplicationPrefix.rowBatchingIndex]; omega) (by omega)).trans hpublic
  refine ⟨w,hselected,?_⟩
  change optionBad (fun packet w answer => packet.bad w answer)
    (RuntimeAdaptiveViews.readBatch binary prime P R cfg S laws hashPublic decodePublic point (point.priorAnswers H)) w (H point).2
  unfold RuntimeAdaptiveViews.readBatch
  rw [hpubEarly]
  change optionBad (fun packet w answer => packet.bad w answer)
    (readBatchPacket currentBinary currentPrime cfg.primeDecode cfg.primeNonzero laws.batchDecoder cfg.primeField cfg.fallback
      point (point.priorAnswers H)) w (H point).2
  unfold readBatchPacket
  rw [hpacket]
  change Prime.BatchBad _ _
  have hd := hs.2.2.1
  have hn := hs.2.2.2.1
  change nd.decode = cfg.primeDecode at hd
  change nd.nonzero = cfg.primeNonzero at hn
  simp only [PrimePacket.frontend]
  rw [← hd,← hn]
  let decoder : BalancedDecoder C (Fin nd.frontend.rows.length → N) :=
    (prime_rows_length currentPrime.setup nd.payload nd.decode nd.nonzero nd.answers).symm ▸ laws.batchDecoder
  change Prime.BatchBad (fun i => (nd.frontend.rows.get i).eval (primeFullValues currentBinary currentPrime w))
    (decoder.decode (H point).2)
  have hcoin : decoder.decode (H point).2 = nd.rho := by
    funext i
    dsimp only [decoder]
    rw [transported_decode (prime_rows_length currentPrime.setup nd.payload nd.decode nd.nonzero nd.answers),
      laws.batch_agrees,hrho,ha]
    rfl
  rwa [hcoin]

theorem rescale_of_late
    (primeGeometry : primePlan.frontend = g.prime)
    (m : ℕ) (hm : m ≤ g.roles.length)
    (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → N)
    (hpublic : RuntimeAdaptiveViews.publics binary prime hashPublic decodePublic
      ((e.chain initialLink).point proof H m) = some (bits,inputs))
    (nd : PrimeData (primeWithInputs prime inputs) C)
    (bd : BinaryData (binaryWithBits binary bits) nd Generator)
    (hread : ApplicationPrefix.readPrime (primeWithInputs prime inputs) cfg.primeField cfg.primeDecode
      cfg.primeNonzero cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some nd)
    (hbinary : ApplicationPrefix.readBinary (binaryWithBits binary bits) nd Generator cfg.packingDegree
      cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion
      cfg.advice cfg.fallback ((e.chain initialLink).point proof H m)
      (((e.chain initialLink).point proof H m).priorAnswers H) = some bd)
    (w : Pair)
    (hselected : S.selected ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H = some w)
    (hbad : Prime.RescalingBad
      (nd.claim.residual (fun i => if (binaryWithBits binary bits).sharedValues w.1 i then 1 else 0)
        (fun i => primeValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w (.inl i)))
      (Handoff.binaryMask ((binaryWithBits binary bits).mask w.1) -
        primeValues (binaryWithBits binary bits) (primeWithInputs prime inputs) w (.inr ())) bd.eta) :
    rescaleBad S (RuntimeAdaptiveViews.readRescale binary prime P R cfg hashPublic decodePublic) laws.rescaleDecoder
      ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g)) H
      (H ((e.chain initialLink).point proof H (ApplicationPrefix.rescalingIndex g))).2 := by
  let index := ApplicationPrefix.rescalingIndex g
  let point := (e.chain initialLink).point proof H index
  let currentBinary := binaryWithBits binary bits
  let currentPrime := primeWithInputs prime inputs
  have hindex : index < g.roles.length := by
    have hh := g.roles_length
    simp only [index,ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at *
    omega
  have hs := ApplicationPrefix.readPrime_spec currentPrime cfg.primeField cfg.primeDecode cfg.primeNonzero
    cfg.fallback _ _ nd hread
  have hb := ApplicationPrefix.readBinary_spec currentBinary nd Generator cfg.packingDegree cfg.binaryField
    cfg.primeField cfg.binaryDecode cfg.binaryNonzero cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback
    _ _ bd hbinary
  have hr := (e.chain initialLink).point_rank proof H hm
  change Input.rank _ = m at hr
  obtain ⟨answer,hanswer,heta⟩ := hb.2.1
  obtain ⟨hpast,ha⟩ := strictAnswer_from_late e initialLink proof H m hm index answer hanswer
  have hw := prime_window prime primePlan primeGeometry
  have hwindow := hs.1
  change g.primeStart+FrontendReplay.slots prime.circuit ≤
    ((e.chain initialLink).point proof H m).rank at hwindow
  rw [hr] at hwindow
  have hprime := ApplicationViewReplay.readPrime_from_late e initialLink proof currentPrime cfg.primeField
    cfg.primeDecode cfg.primeNonzero cfg.fallback H index m hindex.le hm
    (by change g.primeStart+FrontendReplay.slots prime.circuit ≤ index
        rw [hw]; dsimp only [index,ApplicationPrefix.rescalingIndex]; omega)
    hwindow
    (by dsimp only [index,ApplicationPrefix.rescalingIndex]; omega)
    (by dsimp only [index,ApplicationPrefix.rescalingIndex] at hpast; omega) nd hread
  have hpubEarly := (RuntimeAdaptiveReplay.publics_replay_eq binary prime hashPublic decodePublic e initialLink proof H
    index m hindex.le hm (by
      have hh := g.roles_length
      dsimp only [Geometry.primeStart] at *
      omega) (by dsimp only [index,ApplicationPrefix.rescalingIndex,ApplicationPrefix.rowBatchingIndex]; omega)
      (by omega)).trans hpublic
  refine ⟨w,hselected,?_⟩
  change optionBad (fun packet w answer => packet.bad w (laws.rescaleDecoder.decode answer))
    (RuntimeAdaptiveViews.readRescale binary prime P R cfg hashPublic decodePublic point (point.priorAnswers H)) w (H point).2
  unfold RuntimeAdaptiveViews.readRescale
  rw [hpubEarly]
  change optionBad (fun packet w answer => packet.bad w (laws.rescaleDecoder.decode answer))
    (readRescalePacket currentBinary currentPrime cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback
      point (point.priorAnswers H)) w (H point).2
  unfold readRescalePacket
  rw [hprime]
  change Prime.RescalingBad _ _ (laws.rescaleDecoder.decode (H point).2).val
  rw [laws.rescale_agrees]
  rw [heta,ha] at hbad
  exact hbad

end LfzkV2.Current.RuntimeAdaptiveBatch
