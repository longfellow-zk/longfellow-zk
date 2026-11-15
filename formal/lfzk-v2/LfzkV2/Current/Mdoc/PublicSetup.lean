import LfzkV2.Current.Mdoc.Setup
import LfzkV2.Current.SHASetupDomains

noncomputable section

/-! The concrete rate-1/7 public runtime is constructed from the trusted
circuit descriptions and field codecs. All setup and generated-adapter
identifiers read the complementary slice of the same SHA oracle used by
Merkle authentication. Varying Merkle coordinates changes neither setup
nor the causal metadata computation. -/
namespace LfzkV2.Current.Mdoc.PublicSetup
open Application ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

/-- Only the three trusted archive digests are copied from `ids`. Runtime
hashes are computed by the supplied slice of the one SHA oracle. -/
def identifiers (SHA : Bytes → Digest) : MdocIdentifiers.Identifiers :=
  { ids with hash := SHA }

def setup (SHA : Bytes → Digest) :=
  MdocIdentifiers.setup binary prime cantor scalars (identifiers ids SHA) bounds

/-- Shared public protocol setup; no privacy-specific configuration is supplied. -/
abbrev runtime (SHA : Bytes → Digest) :=
  Mdoc.Setup.runtime binary prime cantor scalars (identifiers ids SHA) bounds

abbrev protocol (SHA : Bytes → Digest) :=
  (runtime binary prime cantor scalars ids bounds SHA).protocol

omit [Fintype B] [DecidableEq B] in
theorem setup_merge (outside inside : Bytes → Digest) :
    setup binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      setup binary prime cantor scalars ids bounds outside := by
  unfold setup MdocIdentifiers.setup MdocIdentifiers.binaryContext MdocIdentifiers.primeContext identifiers
  simp only [SHAOracle.context_hash,SHAOracle.joint_context_hash]

end LfzkV2.Current.Mdoc.PublicSetup


/-! The oracle-dependent public setup is selected from a finite family of
digest values. Circuit descriptions, scalar codecs and layout remain fixed.
This family is chosen before sampling the oracle marginal; observer programs
may depend on its public values without exposing an oracle implementation. -/
namespace LfzkV2.Current.Mdoc.SetupFamily
open Application ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxRecDepth 4096

/-- The component contexts also enter causal metadata and may be known to
the observer. Enumerating all four digests fixes a common oracle window;
actual values still come from one SHA function and need not be independent. -/
structure Values where
  fragment : Digest
  binaryContext : Digest
  primeContext : Digest
  jointContext : Digest

instance : Fintype Values := by
  apply Fintype.ofInjective (fun value : Values =>
    (value.fragment,value.binaryContext,value.primeContext,value.jointContext))
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
  fragment := MdocIdentifiers.fragmentId binary scalars (Mdoc.PublicSetup.identifiers ids SHA)
  binaryContext := MdocIdentifiers.binaryContext binary cantor scalars (Mdoc.PublicSetup.identifiers ids SHA)
  primeContext := MdocIdentifiers.primeContext prime scalars (Mdoc.PublicSetup.identifiers ids SHA)
  jointContext := (Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA).jointContext

def setup (visible : Values) : MdocRuntime.FormatSetup :=
  { Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds (fun _ => fun _ => 0) with
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
  simp only [MdocIdentifiers.fragmentId,MdocIdentifiers.binaryContext,MdocIdentifiers.primeContext,
    Mdoc.PublicSetup.identifiers,SHAOracle.context_hash,SHAOracle.fragment_identifier]

end LfzkV2.Current.Mdoc.SetupFamily
