import LfzkV2.Current.ConcreteSetup
import LfzkV2.Current.MdocAdvice
import LfzkV2.Current.IdealRuntime
import LfzkV2.Current.MerkleWireCodec
import LfzkV2.Current.ConcreteMetadata

/-! Fixed public readers for the current mdoc verifier. The only scalar
representations supplied here are the field implementation's canonical
encodings. Advice interpretation, sample projections, row counts and logical
backend coordinates are constructed, rather than supplied as verifier hooks. -/
noncomputable section
namespace LfzkV2.Current.MdocRuntime
open Application ApplicationSetup SumcheckV2
open scoped Classical

abbrev Prime := ZMod Adapter.Mdoc.primeOrder

def fields (B : Type) : Fields
  | .binary => B
  | .prime => Prime

instance {B : Type} [Fintype B] (side : Side) : Fintype (fields B side) := by
  cases side <;> dsimp only [fields,Prime] <;> infer_instance

/-- Scalar codecs belong to the trusted field implementation. Unlike the
old generic representation record, this interface has no advice codec. -/
structure Scalars (B : Type) where
  binary : TranscriptV2.Framing.FieldCodec B
  prime : TranscriptV2.Framing.FieldCodec Prime
  binaryWidth : binary.width = 16
  primeWidth : prime.width = 32

def representations {B : Type} (scalars : Scalars B) :
    ProofBodyCodec.Representations (fields B) MdocAdvice.Value :=
  MdocAdvice.representations scalars.binary scalars.prime scalars.binaryWidth scalars.primeWidth

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]

omit [DecidableEq B] in
/-- A full binary basis fixes the field size; callers do not certify the
security denominator independently of their arithmetic representation. -/
theorem field_card (basis : Module.Basis (Fin 128) (ZMod 2) B) :
    Fintype.card B = Adapter.Mdoc.binaryOrder := by
  simpa [Adapter.Mdoc.binaryOrder] using Fintype.card_congr basis.equivFun.toEquiv

/-- The polynomial-basis element x is the runtime's encoded integer 2.
Its primitive-order checks remain part of application decoding. -/
def polynomialX (basis : Module.Basis (Fin 128) (ZMod 2) B) : Bˣ :=
  Units.mk0 (basis 1) (basis.ne_zero 1)

/-- The conversion uses g=x^(2^128-1-2^64), so g^(-p)=x. The application
decoder validates x before deriving this same fixed power. -/
def generator (basis : Module.Basis (Fin 128) (ZMod 2) B) : Bˣ :=
  polynomialX basis ^ Adapter.Mdoc.generatorExponent

omit [DecidableEq B] in
/-- The runtime's fixed quotient powers start at polynomial x. This equals
the algebraic conversion base for every nonzero x in the field; a separate
primitive-order assumption is unnecessary for this identity. -/
theorem quotient_base (basis : Module.Basis (Fin 128) (ZMod 2) B) :
    generator basis ^ (-(Adapter.Mdoc.primeOrder : ℤ)) = polynomialX basis := by
  have hc : Fintype.card Bˣ = Adapter.Mdoc.groupOrder := by
    rw [Fintype.card_units,field_card basis]
    rfl
  have hm : ((Adapter.Mdoc.generatorExponent : ℤ) * -(Adapter.Mdoc.primeOrder : ℤ)) %
      (Fintype.card Bˣ : ℤ) = 1 := by
    rw [hc]
    norm_num [Adapter.Mdoc.generatorExponent,Adapter.Mdoc.groupOrder,
      Adapter.Mdoc.binaryOrder,Adapter.Mdoc.primeOrder]
  rw [generator,← zpow_natCast,← zpow_mul,← zpow_mod_card,hm,zpow_one]

variable (binary : BinaryPublic B 768 256 10) (prime : PrimePublic Prime 768)
variable (binaryPlan : FrontendSchedule.Plan B binary.template)
variable (primePlan : FrontendSchedule.Plan Prime prime.circuit)

def geometry := ConcreteSetup.geometry binary prime binaryPlan.frontend primePlan.frontend

def binaryCapacity := max binary.degree binaryPlan.capacity
def primeCapacity := max (prime.circuit.layers+1) primePlan.capacity

variable (binaryNodes : Fin 2792 ↪ B)

abbrev binaryBackend := ConcreteSetup.backend binaryNodes binary.cells
abbrev primeBackend := ConcreteSetup.backend ConcreteSetup.primeNodes
  (CellLayout.Prime.cells prime.remaining prime.pads)

abbrev Answer := IdealRuntime.Answer binary prime (binaryBackend binary binaryNodes) (primeBackend prime)
  ((geometry binary prime binaryPlan primePlan).affineRows .binary)
  ((geometry binary prime binaryPlan primePlan).affineRows .prime)
  (binaryCapacity binary binaryPlan) (primeCapacity prime primePlan)

/-- A value for branches outside a valid prefix. Its coordinates never
replace a queried answer on a successfully decoded proof. -/
def fallback : Answer binary prime binaryPlan primePlan binaryNodes
  | .binary => fun _ => 0
  | .binaryNonzero => ⟨1,one_ne_zero⟩
  | .prime => fun _ => 0
  | .primeNonzero => (⟨1,one_ne_zero⟩,⟨1,one_ne_zero⟩)
  | .fingerprints => ((fun _ => 0,fun _ => 0),(fun _ => 0,fun _ => 0))
  | .batching => (fun _ => 0,fun _ => 0)
  | .opening => ⟨Fin.castLE (by decide),Fin.castLE_injective (by decide)⟩

/-- Both verifier arithmetic and derived transcript writes use these same
projections of the one ideal answer. -/
def samples : ConcreteMetadata.Samples B (Answer binary prime binaryPlan primePlan binaryNodes) where
  binary := fun answer index =>
    if h : index < binaryCapacity binary binaryPlan then answer .binary ⟨index,h⟩ else 0
  binaryNonzero := fun answer => answer .binaryNonzero
  prime := fun answer index =>
    if h : index < primeCapacity prime primePlan then answer .prime ⟨index,h⟩ else 0
  primeNonzero := fun answer => (answer .primeNonzero).1
  conversion := fun answer i => Fin.cases (answer .primeNonzero).1 (fun _ => (answer .primeNonzero).2) i
  fallback := fallback binary prime binaryPlan primePlan binaryNodes

variable (scalars : Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64)
variable (privateFits : binary.nPrivate < 2^64)
variable (degreeFits : binary.degree < 2^64)

def shape : WireBlocks.Shape (geometry binary prime binaryPlan primePlan) (fields B) :=
  ConcreteSetup.shape binary prime binaryPlan.frontend primePlan.frontend
    (Equiv.refl _) (Equiv.refl _) inputFits (by decide) privateFits degreeFits

variable (setup : FingerprintPrefix.Setup)
variable (card : Fintype.card B = Adapter.Mdoc.binaryOrder) (polynomialX : Bˣ)

/-- All protocol callbacks are fixed here. In particular the advice decoder
is total on exactly the canonical twenty-bit words admitted by the proof
codec. Canonical wire construction supplies the opening packet encoder. -/
def configuration : RuntimeVerifier.Public
    (g := geometry binary prime binaryPlan primePlan)
    binary prime (binaryBackend binary binaryNodes) (primeBackend prime)
    (fields := fields B) (Advice := MdocAdvice.Value)
    (Base := CanonicalRequest.Base (representations scalars)
      (shape binary prime binaryPlan primePlan inputFits privateFits degreeFits) setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic)
    (C := Answer binary prime binaryPlan primePlan binaryNodes)
    (Salt := MerkleWireCodec.Salt 2443) where
  card := card
  polynomialX := polynomialX
  quotientBound := by decide
  packingDegree := rfl
  binaryField := Equiv.refl _
  primeField := Equiv.refl _
  binaryDecode := (samples binary prime binaryPlan primePlan binaryNodes).binary
  binaryNonzero := (samples binary prime binaryPlan primePlan binaryNodes).binaryNonzero
  primeDecode := (samples binary prime binaryPlan primePlan binaryNodes).prime
  primeNonzero := (samples binary prime binaryPlan primePlan binaryNodes).primeNonzero
  conversion := (samples binary prime binaryPlan primePlan binaryNodes).conversion
  fingerprintBinary := fun answer => (answer .fingerprints).1
  fingerprintPrime := fun answer => (answer .fingerprints).2
  advice := MdocAdvice.decode
  fallback := (samples binary prime binaryPlan primePlan binaryNodes).fallback
  countBinary := (geometry binary prime binaryPlan primePlan).affineRows .binary
  countPrime := (geometry binary prime binaryPlan primePlan).affineRows .prime
  rowDimension := rfl
  maskingDegree := rfl
  binaryRows := rfl
  primeRows := rfl
  openings := rfl
  columns := rfl
  openingPositive := by decide
  openingBase := fun _ => ⟨[],by simp⟩
  initialLink := fun _ => 0
  root := FingerprintPrefix.Key.root
  authenticationContext := fun _ => setup.jointContext
  bindSalt := fun _ column nonce => (column,nonce)
  sample := fun answer => answer .opening

omit [DecidableEq B] in
theorem configuration_advice (value : MdocAdvice.Value) :
    (configuration binary prime binaryPlan primePlan binaryNodes scalars inputFits privateFits degreeFits
      setup card polynomialX).advice value = some (MdocAdvice.bits value) := rfl

omit [DecidableEq B] in
/-- The generic endpoint's ideal-sampling specialization leaves this
already fixed reader unchanged. The transcript metadata uses these same
projections, so it cannot bind claims computed with another sampler. -/
theorem configuration_challenges :
    IdealRuntime.challengePublic binary prime (binaryBackend binary binaryNodes) (primeBackend prime)
      ((geometry binary prime binaryPlan primePlan).affineRows .binary)
      ((geometry binary prime binaryPlan primePlan).affineRows .prime)
      (binaryCapacity binary binaryPlan) (primeCapacity prime primePlan)
      (configuration binary prime binaryPlan primePlan binaryNodes scalars inputFits privateFits degreeFits
        setup card polynomialX) =
    configuration binary prime binaryPlan primePlan binaryNodes scalars inputFits privateFits degreeFits
      setup card polynomialX := rfl

end LfzkV2.Current.MdocRuntime
