import LfzkV2.Current.RuntimeAdaptive
import LfzkV2.Current.RuntimeShape

/-! All adaptive application views read public values from their actual
binding positions. Static topology, cell maps and uniform samplers are shared
by every request; future prime publics are never inserted into the early key. -/
noncomputable section
namespace LfzkV2.Current.RuntimeAdaptiveViews
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
local notation "Pair" => Selection.Pair B N binary.Original prime.Original
local notation "Generator" => cfg.polynomialX^Adapter.Mdoc.generatorExponent

/-- A missing public vector is a rejected parse, not a default statement.
Both values are fixed by the query input before its answer is sampled. -/
def publics (point : Point) : Option ((Fin binary.nPublic → Bool) × (Fin prime.nPublic → N)) := do
  let bits ← hashPublic point.context
  let inputs ← RuntimeAdaptive.primePublic prime decodePublic point
  some (bits,inputs)

def readPrimeView (point : Point) (past : Fin point.rank → C) :
    Option (FrontendView N (Fin prime.pads) Pair Point C) := do
  let values ← publics binary prime hashPublic decodePublic point
  ApplicationViews.readPrimeView (binaryWithBits binary values.1) (primeWithInputs prime values.2)
    primePlan laws.primeCapacity cfg.primeDecode cfg.primeNonzero laws.primeDecoder primeFits
    cfg.primeField cfg.fallback point past

def readBinaryView (point : Point) (past : Fin point.rank → C) :
    Option (FrontendView B binary.Pad Pair Point C) := do
  let values ← publics binary prime hashPublic decodePublic point
  let currentBinary := binaryWithBits binary values.1
  let currentPrime := primeWithInputs prime values.2
  ApplicationViews.readBinaryView currentBinary currentPrime Generator laws.binaryCapacity
    (RuntimeShape.binaryPlan currentBinary currentPrime Generator binaryTemplate)
    cfg.binaryDecode cfg.binaryNonzero laws.binaryDecoder
    (fun packet => by rw [RuntimeShape.binaryPlan_capacity]; exact binaryFits)
    cfg.binaryField cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice
    cfg.fallback point past

def readBatch (point : Point) (past : Fin point.rank → C) :
    Option (BatchPacket N (Fin shared ⊕ prime.Other) Pair C) := do
  let values ← publics binary prime hashPublic decodePublic point
  ApplicationViews.readBatchPacket (binaryWithBits binary values.1) (primeWithInputs prime values.2)
    cfg.primeDecode cfg.primeNonzero laws.batchDecoder cfg.primeField cfg.fallback point past

def readRescale (point : Point) (past : Fin point.rank → C) :
    Option (RescaleData N (Fin shared) prime.Other Pair) := do
  let values ← publics binary prime hashPublic decodePublic point
  ApplicationViews.readRescalePacket (binaryWithBits binary values.1) (primeWithInputs prime values.2)
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback point past

def readConversion (point : Point) (past : Fin point.rank → C) :
    Option (ConversionData Adapter.Mdoc.primeOrder (shared+maskBits) Pair) := do
  let values ← publics binary prime hashPublic decodePublic point
  ApplicationViews.readConversionPacket (binaryWithBits binary values.1) (primeWithInputs prime values.2)
    cfg.primeField cfg.primeDecode cfg.primeNonzero cfg.fallback point past

def readPacking (point : Point) (past : Fin point.rank → C) :
    Option (PackingData (ZMod 2) B (Fin binary.degree) (Fin binary.words) binary.Slot Pair) := do
  let values ← publics binary prime hashPublic decodePublic point
  ApplicationViews.readPackingPacket (binaryWithBits binary values.1) (primeWithInputs prime values.2)
    Generator cfg.packingDegree cfg.binaryField cfg.primeField cfg.binaryDecode cfg.binaryNonzero
    cfg.primeDecode cfg.primeNonzero cfg.conversion cfg.advice cfg.fallback point past

/-- The prime and generated binary frontends keep their original whole-query
bounds after public values are selected adaptively. -/
theorem prime_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (frontendBad S
      (readPrimeView binary prime P R cfg S laws hashPublic decodePublic primePlan primeFits) point H)).card *
        (Fintype.card N-1) ≤ 2*Fintype.card C :=
  frontendBad_card_mul_le S _ point H

theorem binary_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (frontendBad S
      (readBinaryView binary prime P R cfg S laws hashPublic decodePublic binaryTemplate binaryFits) point H)).card *
        (Fintype.card B-1) ≤ 2*Fintype.card C :=
  frontendBad_card_mul_le S _ point H

/-- The remaining four predicates use the existing packet-local bounds.
Their packets carry only already-bound data and fixed-dimension samplers. -/
theorem batch_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (batchBad S (readBatch binary prime P R cfg S laws hashPublic decodePublic) point H)).card *
      Fintype.card N ≤ Fintype.card C :=
  batchBad_card_mul_le S _ point H

theorem rescale_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (rescaleBad S (readRescale binary prime P R cfg hashPublic decodePublic)
      laws.rescaleDecoder point H)).card*(Fintype.card N-1) ≤ Fintype.card C :=
  rescaleBad_card_mul_le S _ laws.rescaleDecoder point H

theorem conversion_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (conversionBad S (readConversion binary prime P R cfg hashPublic decodePublic)
      laws.conversionDecoder Adapter.Mdoc.groupOrder Adapter.Mdoc.quotientBound point H)).card *
      (Adapter.Mdoc.primeOrder-1)^2 ≤
      (2*(Adapter.Mdoc.quotientBound*Adapter.Mdoc.primeOrder/Adapter.Mdoc.groupOrder)+1)^2*Fintype.card C :=
  conversionBad_card_mul_le S _ laws.conversionDecoder
    (by norm_num [Adapter.Mdoc.groupOrder,Adapter.Mdoc.binaryOrder]) laws.bits_le point H

theorem packing_card (point : Point) (H : Point → Digest × C) :
    (Finset.univ.filter (packingBad S (readPacking binary prime P R cfg hashPublic decodePublic)
      laws.packingDecoder point H)).card*Fintype.card B ≤ Fintype.card C :=
  packingBad_card_mul_le S _ laws.packingDecoder point H

end LfzkV2.Current.RuntimeAdaptiveViews
