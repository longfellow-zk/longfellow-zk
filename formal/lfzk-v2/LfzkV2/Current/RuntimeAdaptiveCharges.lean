import LfzkV2.Current.RuntimeAdaptiveViews

/-! Query-local application charging for adaptively chosen public values.
Every reader sees the current preimage and strict earlier answers. Neither
an adversary's future request nor a union of fixed-public events is used. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveCharges
open Application ApplicationSetup ApplicationViews ApplicationOracle ApplicationCharging RecursivePolygero SumcheckV2
open Finset
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Pair" => Selection.Pair B N binary.Original prime.Original

/-- The five concrete prefix readers have common private coordinates and one
query domain. Each parsed frontend carries its checked public shape/samplers;
malformed or unavailable prefixes remain `none`. -/
structure Readers where
  binaryRead : (point : Point) → (Fin point.rank → C) →
    Option (FrontendView B binary.Pad Pair Point C)
  primeRead : (point : Point) → (Fin point.rank → C) →
    Option (FrontendView N (Fin prime.pads) Pair Point C)
  rescaleRead : (point : Point) → (Fin point.rank → C) →
    Option (RescaleData N (Fin shared) prime.Other Pair C)
  conversionRead : (point : Point) → (Fin point.rank → C) →
    Option (ConversionData Adapter.Mdoc.primeOrder (shared+maskBits) Pair)
  packingRead : (point : Point) → (Fin point.rank → C) →
    Option (PackingData (ZMod 2) B (Fin binary.degree) (Fin binary.words) binary.Slot Pair)

variable {Salt Oracle : Type} {k s n t : ℕ}
variable {binary : BinaryPublic B shared maskBits adviceBits} {prime : PrimePublic N shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend N k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable (S : RuntimeSource.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime (Oracle := Oracle))
variable (laws : RuntimeSource.SamplerLaws binary prime P R cfg S)
variable (readers : Readers (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime)

/-- The prime frontend's last boundary, as read by its frontend view. Its
answer also draws `eta`, and its frontend tests are one cancellation. -/
def LastPrime (point : Point) (H : Point → Digest × C) : Prop :=
  point.rank = ApplicationPrefix.rescalingIndex g ∧
    ∀ view, readers.primeRead point (point.priorAnswers H) = some view →
      point.rank+1 = view.data.start+FrontendReplay.slots view.data.circuit

/-- A prime frontend boundary. At the prime frontend's last one the split's
rescaling test shares the answer, and the two are charged as one event. -/
def primeCharge (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  if LastPrime readers point H then
    indicator (frontendBad S readers.primeRead point H answer.2 ∨
      rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2)
  else frontendCharge S readers.primeRead point H answer

theorem primeCharge_last (point : Point) (H : Point → Digest × C) (answer : Digest × C)
    (h : LastPrime readers point H) :
    primeCharge S laws readers point H answer =
      indicator (frontendBad S readers.primeRead point H answer.2 ∨
        rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2) := by
  unfold primeCharge
  exact if_pos h

theorem primeCharge_other (point : Point) (H : Point → Digest × C) (answer : Digest × C)
    (h : ¬ LastPrime readers point H) :
    primeCharge S laws readers point H answer = frontendCharge S readers.primeRead point H answer := by
  unfold primeCharge
  exact if_neg h

/-- Each oracle point has one protocol role. In particular, fragments and
fields do not produce extra independent charges at the same boundary. -/
def roleCharge (role : Role) (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  match role with
  | .fingerprint => indicator (S.binarySelection point H answer.2) + indicator (S.primeSelection point H answer.2)
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .terminal .binary .. | .combine .binary .. => frontendCharge S readers.binaryRead point H answer
  | .inputAssertions .prime .. | .assertions .prime .. | .sumcheck .prime .. |
      .terminal .prime .. | .combine .prime .. => primeCharge S laws readers point H answer
  | .conversion => indicator (conversionBad S readers.conversionRead laws.conversionDecoder
      Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H answer.2)
  | .packing => indicator (packingBad S readers.packingRead laws.packingDecoder point H answer.2)
  | .rowBatching | .batching | .opening => 0

def single (point : Point) (H : Point → Digest × C) (answer : Digest × C) : ℚ :=
  match point.role with
  | some role => roleCharge S laws readers role point H answer
  | none => 0

def budget (LB LN : ℕ) (point : Point) : ℚ :=
  match point.role with
  | some role => roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder
      Adapter.Mdoc.quotientBound LB LN role
  | none => 0

theorem roleCharge_nonneg (role : Role) (point : Point) (H : Point → Digest × C)
    (answer : Digest × C) : 0 ≤ roleCharge S laws readers role point H answer := by
  have hi (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num
  have hp : 0 ≤ primeCharge S laws readers point H answer := by
    unfold primeCharge
    split_ifs
    · exact hi _
    · exact hi _
  cases role with
  | fingerprint => exact add_nonneg (hi _) (hi _)
  | inputAssertions side entries => cases side with
    | binary => exact hi _
    | prime => exact hp
  | assertions side stage entries fragments => cases side with
    | binary => exact hi _
    | prime => exact hp
  | sumcheck side stage index => cases side with
    | binary => exact hi _
    | prime => exact hp
  | terminal side stage => cases side with
    | binary => exact hi _
    | prime => exact hp
  | combine side stage entries fragments last => cases side with
    | binary => exact hi _
    | prime => exact hp
  | conversion | packing => exact hi _
  | rowBatching | batching | opening => exact le_rfl

theorem single_nonneg (point : Point) (H : Point → Digest × C) (answer : Digest × C) :
    0 ≤ single S laws readers point H answer := by
  unfold single
  cases point.role with
  | none => exact le_rfl
  | some role => exact roleCharge_nonneg S laws readers role point H answer

theorem roleCharge_off (role : Role) (point : Point) (H H' : Point → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Digest × C) :
    roleCharge S laws readers role point H answer = roleCharge S laws readers role point H' answer := by
  have hb := propext (S.binarySelection_off point H H' h answer.2)
  have hn := propext (S.primeSelection_off point H H' h answer.2)
  have hbf := frontendCharge_off S readers.binaryRead point H H' h answer
  have hnf := frontendCharge_off S readers.primeRead point H H' h answer
  have hs := propext (packetBad_off S readers.rescaleRead
    (fun packet w a => (∀ a b, (laws.rescaleDecoder.decode a).1 = (laws.rescaleDecoder.decode b).1 →
      packet.claim a = packet.claim b) ∧ packet.bad w a (laws.rescaleDecoder.decode a).2) point H H' h answer.2)
  have hfb := propext (frontendBad_off S readers.primeRead point H H' h answer.2)
  have hlast : LastPrime readers point H ↔ LastPrime readers point H' := by
    unfold LastPrime
    rw [point.priorAnswers_off h]
  have hpf : primeCharge S laws readers point H answer = primeCharge S laws readers point H' answer := by
    unfold primeCharge
    simp only [hlast, rescaleBad, hs, hfb, hnf]
  have hc := propext (packetBad_off S readers.conversionRead
    (fun packet w a => packet.bad Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound w
      (laws.conversionDecoder.decode a)) point H H' h answer.2)
  have hp := propext (packetBad_off S readers.packingRead
    (fun packet w a => packet.bad w (laws.packingDecoder.decode a)) point H H' h answer.2)
  cases role with
  | fingerprint => simp only [roleCharge,hb,hn]
  | inputAssertions side entries => cases side <;> first | exact hbf | exact hpf
  | assertions side stage entries fragments => cases side <;> first | exact hbf | exact hpf
  | sumcheck side stage index => cases side <;> first | exact hbf | exact hpf
  | terminal side stage => cases side <;> first | exact hbf | exact hpf
  | combine side stage entries fragments last => cases side <;> first | exact hbf | exact hpf
  | conversion => simp only [roleCharge,conversionBad,hc]
  | packing => simp only [roleCharge,packingBad,hp]
  | rowBatching | batching | opening => rfl

theorem single_off (point : Point) (H H' : Point → Digest × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Digest × C) :
    single S laws readers point H answer = single S laws readers point H' answer := by
  unfold single
  cases point.role with
  | none => rfl
  | some role => exact roleCharge_off S laws readers role point H H' h answer

theorem single_zero_of_role (point : Point) (H : Point → Digest × C) (answer : Digest × C)
    (hrole : point.role = some .batching ∨ point.role = some .opening) :
    single S laws readers point H answer = 0 := by
  rcases hrole with hrole | hrole <;> simp only [single,hrole,roleCharge]

section Counts
variable {LB LN : ℕ}
variable (binaryListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).1.card ≤ LB)
variable (primeListBound : ∀ (point : RuntimeVerifier.Point (g := g) (fields := fields)
  (Advice := Advice) (Base := Base) (Key := Key)) H,
  (S.lists point.context (S.oracle H point.context)).2.card ≤ LN)
include binaryListBound primeListBound

omit binaryListBound primeListBound in
/-- The fused last prime answer: its frontend tests are one cancellation
(at most `1/(p-1)`) and the rescaling test is another, within the existing
`2/(p-1)` prime budget. Elsewhere the frontend alone has `2/(p-1)`. -/
theorem primeCharge_sum (point : Point) (H : Point → Digest × C) :
    (∑ answer, primeCharge S laws readers point H answer) ≤
      Fintype.card (Digest × C) * (2/((Fintype.card N-1 : ℕ) : ℚ)) := by
  by_cases hlast : LastPrime readers point H
  · rw [Finset.sum_congr rfl (fun answer _ => primeCharge_last S laws readers point H answer hlast)]
    have hpos : 0 < Fintype.card N-1 := Nat.sub_pos_of_lt Fintype.one_lt_card
    have hf := indicator_link_sum_le (Link := Digest) (frontendBad S readers.primeRead point H) 1
      (Fintype.card N-1) hpos (by simpa only [one_mul] using
        frontendBad_card_mul_le_last S readers.primeRead point H hlast.2)
    have hr := indicator_link_sum_le (Link := Digest)
      (rescaleBad S readers.rescaleRead laws.rescaleDecoder point H) 1 (Fintype.card N-1) hpos
      (by simpa only [one_mul] using rescaleBad_card_mul_le S readers.rescaleRead laws.rescaleDecoder point H)
    have hle : ∀ answer : Digest × C,
        indicator (frontendBad S readers.primeRead point H answer.2 ∨
          rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2) ≤
        indicator (frontendBad S readers.primeRead point H answer.2) +
          indicator (rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2) := by
      intro answer
      unfold indicator
      split_ifs <;> simp_all
    calc _ ≤ ∑ answer : Digest × C, (indicator (frontendBad S readers.primeRead point H answer.2) +
            indicator (rescaleBad S readers.rescaleRead laws.rescaleDecoder point H answer.2)) :=
          Finset.sum_le_sum fun answer _ => hle answer
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add hf hr
      _ = _ := by ring
  · rw [Finset.sum_congr rfl (fun answer _ => primeCharge_other S laws readers point H answer hlast)]
    exact frontendCharge_sum S readers.primeRead point H

theorem roleCharge_sum (role : Role) (point : Point) (H : Point → Digest × C) :
    (∑ answer, roleCharge S laws readers role point H answer) ≤ Fintype.card (Digest × C) *
      roundBudget B Adapter.Mdoc.primeOrder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound LB LN role := by
  have hB : 0 < Fintype.card B-1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hp : 0 < Adapter.Mdoc.primeOrder-1 := Nat.sub_pos_of_lt (Fact.out : Adapter.Mdoc.primeOrder.Prime).one_lt
  have hbcount := (S.binarySelection_card_mul_le laws.binarySelectionDecoder
    laws.binarySelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (binaryListBound point H)))
  have hncount := (S.primeSelection_card_mul_le laws.primeSelectionDecoder
    laws.primeSelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (primeListBound point H)))
  have hb := indicator_link_sum_le (Link := Digest) (S.binarySelection point H)
    (LB.choose 2) (Fintype.card B^2) (by positivity) hbcount
  have hn := indicator_link_sum_le (Link := Digest) (S.primeSelection point H)
    (LN.choose 2) (Adapter.Mdoc.primeOrder^2) (by norm_num [Adapter.Mdoc.primeOrder])
    (by simpa only [ZMod.card] using hncount)
  have hbf := frontendCharge_sum S readers.binaryRead point H
  have hnf := primeCharge_sum S laws readers point H
  have hc := indicator_link_sum_le (Link := Digest)
    (conversionBad S readers.conversionRead laws.conversionDecoder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H)
    ((2*(Adapter.Mdoc.quotientBound*Adapter.Mdoc.primeOrder/Adapter.Mdoc.groupOrder)+1)^2)
    ((Adapter.Mdoc.primeOrder-1)^2) (by positivity)
    (conversionBad_card_mul_le S readers.conversionRead laws.conversionDecoder
      (by norm_num [Adapter.Mdoc.groupOrder,Adapter.Mdoc.binaryOrder]) laws.bits_le point H)
  have hpack := indicator_link_sum_le (Link := Digest) (packingBad S readers.packingRead laws.packingDecoder point H)
    1 (Fintype.card B) Fintype.card_pos
    (by simpa only [one_mul] using packingBad_card_mul_le S readers.packingRead laws.packingDecoder point H)
  cases role with
  | fingerprint =>
      simp only [roleCharge,sum_add_distrib,roundBudget]
      exact (add_le_add hb hn).trans_eq (by push_cast; ring)
  | inputAssertions side entries => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | assertions side stage entries fragments => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | sumcheck side stage index => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | terminal side stage => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | combine side stage entries fragments last => cases side with
      | binary => exact hbf
      | prime => simpa only [roleCharge,roundBudget,ZMod.card] using hnf
  | conversion => simpa only [roleCharge,roundBudget,Nat.cast_pow] using hc
  | packing => exact hpack
  | rowBatching | batching | opening => simp only [roleCharge,roundBudget,sum_const_zero,mul_zero,le_refl]

theorem single_sum (point : Point) (H : Point → Digest × C) :
    (∑ answer, single S laws readers point H answer) ≤ Fintype.card (Digest × C)*budget (B := B) LB LN point := by
  unfold single budget
  cases point.role with
  | none => simp only [sum_const_zero,mul_zero,le_refl]
  | some role => exact roleCharge_sum S laws readers binaryListBound primeListBound role point H

end Counts

/-- The runtime's five optional readers are constructed directly from the
bound public-value parsers and the two fixed public frontend plans. -/
def concreteReaders (hashPublic : Key → Option (Fin binary.nPublic → Bool))
    (decodePublic : Base → Option (Fin prime.nPublic → N))
    (primePlan : FrontendSchedule.Plan N prime.circuit)
    (primeFits : primePlan.capacity ≤ laws.primeCapacity)
    (binaryPlan : FrontendSchedule.Plan B binary.circuit)
    (binaryFits : binaryPlan.capacity ≤ laws.binaryCapacity) :
    Readers (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) (C := C)
      binary prime where
  binaryRead := RuntimeAdaptiveViews.readBinaryView binary prime P R cfg S laws hashPublic decodePublic
    binaryPlan binaryFits
  primeRead := RuntimeAdaptiveViews.readPrimeView binary prime P R cfg S laws hashPublic decodePublic
    primePlan primeFits
  rescaleRead := RuntimeAdaptiveViews.readRescale binary prime P R cfg hashPublic decodePublic
  conversionRead := RuntimeAdaptiveViews.readConversion binary prime P R cfg hashPublic decodePublic
  packingRead := RuntimeAdaptiveViews.readPacking binary prime P R cfg hashPublic decodePublic

end LfzkV2.Current.RuntimeAdaptiveCharges
