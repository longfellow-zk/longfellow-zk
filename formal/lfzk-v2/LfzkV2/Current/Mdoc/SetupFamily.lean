import LfzkV2.Current.Mdoc.PublicSetup

/-! The oracle-dependent public setup is selected from a finite family of
digest values. Circuit descriptions, scalar codecs and layout remain fixed.
This family is chosen before sampling the oracle marginal; observer programs
may depend on its public values without exposing an oracle implementation. -/
noncomputable section
namespace LfzkV2.Current.Mdoc.SetupFamily
open Application ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxRecDepth 4096

/-- The component contexts also enter causal metadata and may be known to
the observer. Enumerating all four digests fixes a common oracle window;
actual values still come from one SHA function and need not be independent. -/
structure Values where
  hashTemplate : Digest
  binaryContext : Digest
  primeContext : Digest
  jointContext : Digest

instance : Fintype Values := by
  apply Fintype.ofInjective (fun value : Values =>
    (value.hashTemplate,value.binaryContext,value.primeContext,value.jointContext))
  intro first second same
  cases first
  cases second
  cases same
  rfl

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

def values (SHA : Bytes → Digest) : Values where
  hashTemplate := (Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA).hashTemplate
  binaryContext := MdocIdentifiers.binaryContext binary cantor scalars (Mdoc.PublicSetup.identifiers ids SHA)
  primeContext := MdocIdentifiers.primeContext prime scalars (Mdoc.PublicSetup.identifiers ids SHA)
  jointContext := (Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA).jointContext

def setup (visible : Values) : FingerprintPrefix.Setup :=
  { Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds (fun _ => fun _ => 0) with
    hashTemplate := visible.hashTemplate
    jointContext := visible.jointContext }

omit [Fintype B] [DecidableEq B] in
theorem setup_values (SHA : Bytes → Digest) :
    Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA =
      setup binary prime cantor scalars ids bounds (values binary prime cantor scalars ids bounds SHA) := rfl

omit [Fintype B] [DecidableEq B] in
theorem values_merge (outside inside : Bytes → Digest) :
    values binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      values binary prime cantor scalars ids bounds outside := by
  have same := Mdoc.PublicSetup.setup_merge binary prime cantor scalars ids bounds outside inside
  unfold values
  rw [same]
  simp only [MdocIdentifiers.binaryContext,MdocIdentifiers.primeContext,Mdoc.PublicSetup.identifiers,
    SHAOracle.context_hash]

local notation "Shape" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "Repr" => MdocRuntime.representations scalars

abbrev Point (visible : Values) :=
  QueryRuntime.Runtime.Point Repr Shape (setup binary prime cantor scalars ids bounds visible) binary.nPublic

abbrev Canonical (visible : Values) (point : Point binary prime cantor scalars ids bounds visible) : Prop :=
  QueryRuntime.Runtime.Canonical Repr Shape (setup binary prime cantor scalars ids bounds visible) binary.nPublic point

abbrev pointFintype (visible : Values) : Fintype (Point binary prime cantor scalars ids bounds visible) := inferInstance

def codec (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
    (visible : Values) : ByteOracleTransport.Codec (Point binary prime cantor scalars ids bounds visible) Bytes
      (Canonical binary prime cantor scalars ids bounds visible) :=
  QueryRuntime.Runtime.codec Repr Shape (setup binary prime cantor scalars ids bounds visible) binary.nPublic fits

end LfzkV2.Current.Mdoc.SetupFamily
