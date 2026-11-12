import LfzkV2.Current.IdealSamples
import LfzkV2.Current.RuntimeBackend
import LfzkV2.Current.OpeningSampling

/-! Runtime challenge readers on the common finite ideal answer. All
uniformity statements below are constructed from product projections; byte
rejection is covered by the explicit ideal-sampler oracle assumption. The
byte-stream coupling is separate. Shared prefixes retain the same coordinate
accessors. -/
noncomputable section
namespace LfzkV2.Current.IdealRuntime
open Application ApplicationSetup
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Base Key B Salt : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)

abbrev RawBinary := Fin (BackendChallenges.size countBinary P.backend.nw P.backend.s) → B
abbrev RawPrime := Fin (BackendChallenges.size countPrime R.backend.nw R.backend.s) → N
abbrev Answer := IdealSamples.Answer B N binary.Original prime.Original
  (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity

def component (kind : IdealSamples.Component) :=
  IdealSamples.decoder B N binary.Original prime.Original
    (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity kind

def primeNonzero := IdealSamples.primeNonzeroDecoder B N binary.Original prime.Original
  (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity

def fingerprintBinary := IdealSamples.fingerprintBinaryDecoder B N binary.Original prime.Original
  (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity

def fingerprintPrime := IdealSamples.fingerprintPrimeDecoder B N binary.Original prime.Original
  (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity

variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
  (C := Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Salt))

/-- Arithmetic/layout setup is retained. Every challenge callback is the
corresponding exact projection from the one common ideal answer. -/
def challengePublic : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
    (Base := Base) (Key := Key)
    (C := Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Salt) :=
  { cfg with
    countBinary := countBinary
    countPrime := countPrime
    binaryDecode := fun answer index =>
      if hi : index < binaryCapacity then answer .binary ⟨index,hi⟩ else 0
    binaryNonzero := fun answer => answer .binaryNonzero
    primeDecode := fun answer index =>
      if hi : index < primeCapacity then answer .prime ⟨index,hi⟩ else 0
    primeNonzero := fun answer => (answer .primeNonzero).1
    conversion := fun answer i => Fin.cases (answer .primeNonzero).1
      (fun _ => (answer .primeNonzero).2) i
    fingerprintBinary := fun answer => (answer .fingerprints).1
    fingerprintPrime := fun answer => (answer .fingerprints).2
    sample := fun answer => answer .opening }

def draw : Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity →
    RuntimeVerifier.RawSamples binary prime P R
      (challengePublic binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg) :=
  fun answer => answer .batching

def rawSampler : BalancedDecoder
    (Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (RuntimeVerifier.RawSamples binary prime P R
      (challengePublic binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg)) :=
  component binary prime P R countBinary countPrime binaryCapacity primeCapacity .batching

theorem rawSampler_decode :
    (rawSampler binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg).decode =
      draw binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg := rfl

def querySampler : BalancedDecoder
    (Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
    (LigeroFamily.QuerySet n t) :=
  OpeningSampling.decoder
    (IdealSamples.factor B N binary.Original prime.Original
      (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n)
      binaryCapacity primeCapacity .opening)

theorem querySampler_decode :
    (querySampler binary prime P R countBinary countPrime binaryCapacity primeCapacity).decode =
      RuntimeBackend.queryDecoder binary prime P R
        (challengePublic binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg) := rfl

variable {Oracle : Type}
variable (source : RuntimeCover.Source (g := g) (fields := fields) (Advice := Advice) (Base := Base)
  (Key := Key) (C := Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity)
  binary prime (Oracle := Oracle))

/-- The source's coin function is definitionally this projection for the
runtime's constructed selection source. No statement or list bound occurs
in this sampler constructor. -/
def samplerLaws
    (sourceCoins : source.coins = fun answer => ((answer .fingerprints).1,(answer .fingerprints).2))
    (binaryFits : binary.degree ≤ binaryCapacity)
    (primeFits : prime.circuit.layers+1 ≤ primeCapacity)
    (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound) :
    RuntimeCover.SamplerLaws binary prime P R
      (challengePublic binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg) source where
  binaryCapacity := binaryCapacity
  primeCapacity := primeCapacity
  binaryDecoder := IdealSamples.binaryFrontend B N binary.Original prime.Original
    (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity
    (by have := binary.degree_gt; omega)
  primeDecoder := IdealSamples.primeFrontend B N binary.Original prime.Original
    (RawBinary P countBinary) (RawPrime R countPrime) (Fin t ↪ Fin n) binaryCapacity primeCapacity (by omega)
  batchDecoder := IdealSamples.vectorBlock
    (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .prime)
    0 (prime.circuit.layers+1) (by omega)
  batch_agrees answer i := by
    change _ = IdealSamples.vectorRead
      (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .prime) answer i.val
    simpa only [Nat.zero_add] using congrFun (congrFun
      (IdealSamples.vectorBlock_decode
        (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .prime)
        0 (prime.circuit.layers+1) (by omega)) answer) i
  rescaleDecoder := primeNonzero binary prime P R countBinary countPrime binaryCapacity primeCapacity
  rescale_agrees := rfl
  conversionDecoder := component binary prime P R countBinary countPrime binaryCapacity primeCapacity .primeNonzero
  conversion_agrees answer := rfl
  packingDecoder := IdealSamples.vectorBlock
    (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .binary)
    0 binary.degree (by omega)
  packing_agrees answer i := by
    change _ = IdealSamples.vectorRead
      (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .binary) answer i.val
    simpa only [Nat.zero_add] using congrFun (congrFun
      (IdealSamples.vectorBlock_decode
        (component binary prime P R countBinary countPrime binaryCapacity primeCapacity .binary)
        0 binary.degree (by omega)) answer) i
  binarySelectionDecoder := fingerprintBinary binary prime P R countBinary countPrime binaryCapacity primeCapacity
  primeSelectionDecoder := fingerprintPrime binary prime P R countBinary countPrime binaryCapacity primeCapacity
  binarySelection_agrees answer := by
    exact (congrArg (fun f => (f answer).1) sourceCoins).symm
  primeSelection_agrees answer := by
    exact (congrArg (fun f => (f answer).2) sourceCoins).symm
  bits_le := bitsFit

end LfzkV2.Current.IdealRuntime
