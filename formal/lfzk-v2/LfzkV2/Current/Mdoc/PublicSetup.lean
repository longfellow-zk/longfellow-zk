import LfzkV2.Current.Mdoc.Setup
import LfzkV2.Current.SHAOracle
import LfzkV2.Current.MdocIdentifiers

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

omit [Fintype B] [DecidableEq B] in
theorem setup_merge (outside inside : Bytes → Digest) :
    setup binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      setup binary prime cantor scalars ids bounds outside := by
  have same : MdocIdentifiers.fragmentId binary scalars
      (identifiers ids (SHAOracle.merge SHAOracle.merkleDomain outside inside)) =
        MdocIdentifiers.fragmentId binary scalars (identifiers ids outside) := by
    simp only [MdocIdentifiers.fragmentId,identifiers,SHAOracle.fragment_identifier]
  unfold setup MdocIdentifiers.setup
  rw [same]
  rfl

end LfzkV2.Current.Mdoc.PublicSetup


/-! The oracle-dependent public values form a finite family of digests.
Circuit descriptions, scalar codecs and layout remain fixed; the format setup
reads only the adapter fragment identifier, which its statement binds, as one
of these values. This family is chosen before sampling the
oracle marginal; observer programs may depend on its public values without
exposing an oracle implementation. -/
namespace LfzkV2.Current.Mdoc.SetupFamily
open Application ApplicationSetup ConcreteSetup
open scoped Classical
set_option maxRecDepth 4096

/-- The adapter fragment identifier enters causal metadata and may be known
to the observer. Enumerating its digest fixes a common oracle window. -/
structure Values where
  fragment : Digest

instance : Fintype Values := by
  apply Fintype.ofInjective (fun value : Values => value.fragment)
  intro first second same
  cases first
  cases second
  cases same
  rfl

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

/-- The public values on `SHA`. They read neither the signature circuit,
the basis nor the bounds, which keep the family's common signature. -/
def values (_prime : PrimeCircuit) (_cantor : Module.Basis (Fin 128) (ZMod 2) B)
    (scalars : MdocRuntime.Scalars B) (ids : MdocIdentifiers.Identifiers)
    (_bounds : MdocIdentifiers.Bounds binary _prime) (SHA : Bytes → Digest) : Values where
  fragment := MdocIdentifiers.fragmentId binary scalars (Mdoc.PublicSetup.identifiers ids SHA)

/-- The format setup of the family member with public values `visible`: its
statement binds the member's adapter fragment identifier. -/
def setup (visible : Values) : MdocRuntime.FormatSetup :=
  MdocIdentifiers.setupOf binary prime cantor scalars ids bounds visible.fragment

omit [Fintype B] [DecidableEq B] in
theorem values_merge (outside inside : Bytes → Digest) :
    values binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      values binary prime cantor scalars ids bounds outside := by
  unfold values
  simp only [MdocIdentifiers.fragmentId,Mdoc.PublicSetup.identifiers,SHAOracle.fragment_identifier]

end LfzkV2.Current.Mdoc.SetupFamily
