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

def metadata (SHA : Bytes → Digest) :=
  ConcreteMetadata.metadata
    (g := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan)
    (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (C := MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    binary.description prime.description
    (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
      (by change 128 < 2^64; decide))
    (MdocIdentifiers.parameters binary prime cantor scalars (identifiers ids SHA) bounds)
    (setup binary prime cantor scalars ids bounds SHA)

omit [Fintype B] [DecidableEq B] in
theorem setup_merge (outside inside : Bytes → Digest) :
    setup binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      setup binary prime cantor scalars ids bounds outside := by
  unfold setup MdocIdentifiers.setup MdocIdentifiers.fragmentId MdocIdentifiers.binaryContext MdocIdentifiers.primeContext identifiers
  simp only [SHAOracle.fragment_identifier,SHAOracle.context_hash,SHAOracle.joint_context_hash]

omit [Fintype B] [DecidableEq B] in
theorem metadata_merge (outside inside : Bytes → Digest) :
    metadata binary prime cantor scalars ids bounds (SHAOracle.merge SHAOracle.merkleDomain outside inside) =
      metadata binary prime cantor scalars ids bounds outside := by
  have sameSetup := setup_merge binary prime cantor scalars ids bounds outside inside
  dsimp only [setup,identifiers] at sameSetup
  unfold metadata setup ConcreteMetadata.metadata
  funext request index writes past
  simp only [MdocIdentifiers.parameters,MdocIdentifiers.binaryContext,MdocIdentifiers.primeContext,identifiers,
    SHAOracle.context_hash,sameSetup,
    ConcreteMetadata.start,ConcreteMetadata.role]

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
  fragment := (Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA).fragment
  binaryContext := MdocIdentifiers.binaryContext binary cantor scalars (Mdoc.PublicSetup.identifiers ids SHA)
  primeContext := MdocIdentifiers.primeContext prime scalars (Mdoc.PublicSetup.identifiers ids SHA)
  jointContext := (Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds SHA).jointContext

def setup (visible : Values) : FingerprintPrefix.Setup :=
  { Mdoc.PublicSetup.setup binary prime cantor scalars ids bounds (fun _ => fun _ => 0) with
    fragment := visible.fragment
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

end LfzkV2.Current.Mdoc.SetupFamily
