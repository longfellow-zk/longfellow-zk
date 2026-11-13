import LfzkV2.Current.MdocRuntime

/-! Exact setup bytes for the current mdoc verifier. Trusted circuit identifiers
and the identifier hash are inputs; layouts, field identities, packing metadata,
backend contexts and the archived adapter fragment identifier are constructed here.
These are ordinary auxiliary hash inputs, not additional transcript queries. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.MdocIdentifiers
open Application ApplicationSetup
open CanonicalPrefix (utf8)
open TranscriptV2.Framing (encodeLE)
open scoped Classical

structure Identifiers where
  combinedHash : Digest
  hashCircuit : Digest
  primeCircuit : Digest
  hash : Bytes → Digest

def binaryField : Bytes := utf8 "GF2[x]/(x^128+x^7+x^2+x+1)/polynomial/v1"

def primeField {B : Type} (scalars : MdocRuntime.Scalars B) : Bytes :=
  utf8 "prime/canonical-integer/v1/" ++ scalars.prime.encode (-1)

private def part (bytes : Bytes) : Bytes := encodeLE 8 bytes.length ++ bytes

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)

def packingDescriptor : Bytes :=
  utf8 "longfellow/packing-extension/v1" ++ part binaryField ++
    part (utf8 "GF2-to-GF128/polynomial/v1") ++ part (encodeLE 8 128) ++
    (List.ofFn fun i : Fin 128 => scalars.binary.encode (binary.basis i)).flatten

def binaryDomain : Bytes :=
  utf8 "gf2_128/lch14-prefix/v1" ++
    (List.ofFn fun i : Fin 128 => scalars.binary.encode (cantor i)).flatten

def primeDomain : Bytes :=
  utf8 "prime/arithmetic-prefix/v1" ++ scalars.prime.encode (-1)

/-- Rust's geometry header stores the augmented cell count `nw`, including
the two selector masks. The backend model separately rounds this count into
265-cell rows; that row count is not the first word of this hash input. -/
def contextBytes (domain : Bytes) (witnessCells : ℕ) : Bytes :=
  utf8 "polygero/root/context/linear/v1" ++ part domain ++
    [witnessCells,349,12,2443,84].flatMap (encodeLE 8)

def binaryContext (ids : Identifiers) : Digest :=
  ids.hash (contextBytes (binaryDomain cantor scalars) (binary.description.cells+2))

def primeContext (ids : Identifiers) : Digest :=
  ids.hash (contextBytes (primeDomain scalars)
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads+2))

def jointContextBytes (binary prime : Digest) : Bytes :=
  utf8 "polygero/joint/context/v1" ++ encodeLE 8 16 ++ List.ofFn binary ++
    encodeLE 8 32 ++ List.ofFn prime ++ encodeLE 8 2

/-- Component zero is the trusted hash circuit. Empty sparse fragments still
identify an active layer, so depth is determined by layer presence rather than
the number of gates or the fragment's local layer tag. -/
def hashDepth : ℕ := binary.plan.frontend.stages.countP fun stage =>
  stage.fragments.any fun fragment => fragment.circuit == 0

/-- Only public shape, allocation and fixed-width serialization bounds remain.
None is an acceptance, decoding or soundness certificate. -/
structure Bounds where
  inputFits : 768+prime.description.remaining+prime.description.pads < 2^64
  privateFits : binary.description.nPrivate < 2^64
  padsFit : binary.description.pads < 2^64
  binaryCellsFit : binary.description.cells+2 < 2^64
  primeCellsFit : CellLayout.Prime.cells prime.description.remaining prime.description.pads+2 < 2^64
  layerFits : ∀ stage ∈ binary.plan.frontend.stages, stage.rounds < 2^64
  primeLayerFits : ∀ stage ∈ prime.plan.frontend.stages, stage.rounds < 2^64
  /-- The committed binary inputs, and so every storage address, fit a word. -/
  committedFit : binary.nPublic+binary.nPrivate < 2^64
  hashDepthFit : hashDepth binary < 2^64
  /-- This concrete topology places the hash first and admits the adapter's
  outputs at a later layer. A tied or shorter hash needs a different topology
  constructor, including the corresponding hash output-entry block. -/
  adapterDepth_lt_hashDepth :
    (MetadataIdentifiers.reductions (F := B) binary.description.shape).length+2 < hashDepth binary
  primeDepthFit : prime.description.circuit.layers < 2^64
  adapterDepthFit : (MetadataIdentifiers.reductions (F := B) binary.description.shape).length+2 < 2^64
  binaryRowsFit : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).affineRows .binary < 2^64
  primeRowsFit : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).affineRows .prime < 2^64

private def boundedBinaryField : BoundedBytes CanonicalPrefix.maxLength :=
  ⟨binaryField,by decide⟩

private def boundedPrimeField : BoundedBytes CanonicalPrefix.maxLength :=
  ⟨primeField scalars,by
    simp only [primeField,List.length_append,scalars.prime.length,scalars.primeWidth]
    decide⟩

private def boundedPacking : BoundedBytes CanonicalPrefix.maxLength :=
  ⟨packingDescriptor binary scalars,by
    simp only [packingDescriptor,List.length_append,List.length_flatten,List.map_ofFn,
      Function.comp_def,scalars.binary.length,scalars.binaryWidth]
    decide⟩

/-- Identifier of the archived adapter fragment, rebuilt from the hash
circuit's shape: its virtual leaves start after the committed inputs. -/
def fragmentId (ids : Identifiers) : Digest :=
  MetadataIdentifiers.fragmentId ids.hash scalars.binary.encode binary.description.shape
    (binary.nPublic+binary.nPrivate+2*(768+256+10)) binary.nPublic (binary.nPublic+binary.nPrivate)

private def word (value : ℕ) (fits : value < 2^64) : FingerprintPrefix.Word := ⟨value,fits⟩

/-- The signature participant's storage map as runs (`StorageMap::runs`).
Its values are `[private inputs | pads]`: the issuer digest's 256 bits, then
device x and y (512 bits after the MSO preimage), each a one-bit prime group
in the binary inputs; every other value is native, in value order. R's 256
bits follow the hash circuit's own inputs. Each word is its own write. -/
def storageWords (bounds : Bounds binary prime) : List FingerprintPrefix.Word :=
  have hc := bounds.committedFit
  have hn : binary.nPublic+20760 < 2^64 := by
    have := binary.hashCapacity
    unfold ConcreteSetup.BinaryCircuit.nPrivate at hc
    omega
  have hh : binary.nPublic+binary.hashPrivate < 2^64 := by
    unfold ConcreteSetup.BinaryCircuit.nPrivate at hc
    omega
  have hr : prime.description.remaining+prime.description.pads < 2^64 := by
    have := bounds.inputFits
    omega
  [word 3 (by decide),
    word 1 (by decide),word 0 (by decide),word 256 (by decide),word binary.nPublic (by omega),word 1 (by decide),
    word 1 (by decide),word 256 (by decide),word 512 (by decide),word (binary.nPublic+20760) hn,word 1 (by decide),
    word 0 (by decide),word 768 (by decide),
      word (prime.description.remaining+prime.description.pads) hr,word 0 (by decide),
    word (binary.nPublic+binary.hashPrivate) hh,word 256 (by decide)]

def setup (ids : Identifiers) (bounds : Bounds binary prime) : FingerprintPrefix.Setup where
  combinedHash := ids.combinedHash
  hashCircuit := ids.hashCircuit
  fragment := fragmentId binary scalars ids
  primeCircuit := ids.primeCircuit
  packingDescriptor := boundedPacking binary scalars
  privateInputs := ⟨binary.description.nPrivate,bounds.privateFits⟩
  padCells := ⟨binary.description.pads,bounds.padsFit⟩
  layerWidths := binary.plan.frontend.stages.attach.map fun stage => ⟨stage.val.rounds,bounds.layerFits _ stage.property⟩
  primeLayerWidths := prime.plan.frontend.stages.attach.map fun stage =>
    ⟨stage.val.rounds,bounds.primeLayerFits _ stage.property⟩
  storage := storageWords binary prime bounds
  jointContext := ids.hash (jointContextBytes (binaryContext binary cantor scalars ids) (primeContext prime scalars ids))
  binaryField := boundedBinaryField
  primeField := boundedPrimeField scalars
  binaryCells := ⟨binary.description.cells,by have := bounds.binaryCellsFit; omega⟩
  primeCells := ⟨CellLayout.Prime.cells prime.description.remaining prime.description.pads,by
    have := bounds.primeCellsFit; omega⟩

def parameters (ids : Identifiers) (bounds : Bounds binary prime) :
    ConcreteMetadata.Public binary.description prime.description
      (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)) where
  binaryCount := rfl
  primeCount := rfl
  primeInputs := rfl
  sharedBits := rfl
  packingInputs := rfl
  binary128 := rfl
  binaryPadsFit := bounds.padsFit
  primeDepthFit := bounds.primeDepthFit
  adapterDepthFit := bounds.adapterDepthFit
  binaryRowsFit := bounds.binaryRowsFit
  primeRowsFit := bounds.primeRowsFit
  hashDepth := ⟨hashDepth binary,bounds.hashDepthFit⟩
  binaryContext := binaryContext binary cantor scalars ids
  primeContext := primeContext prime scalars ids

end LfzkV2.Current.MdocIdentifiers
