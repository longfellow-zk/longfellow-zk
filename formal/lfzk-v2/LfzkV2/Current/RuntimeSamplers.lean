import LfzkV2.Current.RuntimeCover

/-! Runtime sampling laws are independent of the commitment extractor. Only
the fixed fingerprint-coin decoder appears in their selection agreements. -/
namespace LfzkV2.Current.RuntimeCover.SamplerLaws
open Application ApplicationSetup ApplicationOracle RecursivePolygero

variable {g : Geometry} {fields : Fields} {Advice Base Key C B Salt Oracle : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] [Fintype C]
variable {shared maskBits adviceBits k s n t : ℕ}
variable {binary : BinaryPublic B shared maskBits adviceBits}
variable {prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) shared}
variable {P : FieldBackend B k s n t} {R : FieldBackend (ZMod Adapter.Mdoc.primeOrder) k s n t}
variable {cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Salt)}
variable {S : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := C) binary prime (Oracle := Oracle)}

/-- Retain every sampler and public capacity when changing only the recovered
commitment oracle. Equal coefficient decoders make both agreements transport. -/
def retarget (laws : SamplerLaws binary prime P R cfg S)
    (T : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
      (Key := Key) (C := C) binary prime (Oracle := Oracle))
    (hcoins : S.coins = T.coins) : SamplerLaws binary prime P R cfg T where
  primeCapacity := laws.primeCapacity
  binaryCapacity := laws.binaryCapacity
  primeDecoder := laws.primeDecoder
  binaryDecoder := laws.binaryDecoder
  batchDecoder := laws.batchDecoder
  batch_agrees := laws.batch_agrees
  rescaleDecoder := laws.rescaleDecoder
  rescale_agrees := laws.rescale_agrees
  conversionDecoder := laws.conversionDecoder
  conversion_agrees := laws.conversion_agrees
  packingDecoder := laws.packingDecoder
  packing_agrees := laws.packing_agrees
  binarySelectionDecoder := laws.binarySelectionDecoder
  primeSelectionDecoder := laws.primeSelectionDecoder
  binarySelection_agrees answer := (laws.binarySelection_agrees answer).trans (congrArg (fun f => (f answer).1) hcoins)
  primeSelection_agrees answer := (laws.primeSelection_agrees answer).trans (congrArg (fun f => (f answer).2) hcoins)
  bits_le := laws.bits_le

/-- The source's recovered oracle is irrelevant to the public sampler
dimensions. Expose those projections without unfolding a concrete source. -/
theorem retarget_primeCapacity (laws : SamplerLaws binary prime P R cfg S)
    (T : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
      (Key := Key) (C := C) binary prime (Oracle := Oracle))
    (hcoins : S.coins = T.coins) :
    (laws.retarget T hcoins).primeCapacity = laws.primeCapacity := rfl

theorem retarget_binaryCapacity (laws : SamplerLaws binary prime P R cfg S)
    (T : Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
      (Key := Key) (C := C) binary prime (Oracle := Oracle))
    (hcoins : S.coins = T.coins) :
    (laws.retarget T hcoins).binaryCapacity = laws.binaryCapacity := rfl

end LfzkV2.Current.RuntimeCover.SamplerLaws
