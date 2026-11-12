import LfzkV2.Current.SHASetupDomains
import LfzkV2.Current.Mdoc.Setup

/-! The concrete rate-1/7 public runtime is constructed from the trusted
circuit descriptions and field codecs. All setup and generated-adapter
identifiers read the complementary slice of the same SHA oracle used by
Merkle authentication. Varying Merkle coordinates changes neither setup
nor the causal metadata computation. -/
noncomputable section
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
  unfold setup MdocIdentifiers.setup MdocIdentifiers.templateId MdocIdentifiers.binaryContext MdocIdentifiers.primeContext identifiers
  simp only [SHAOracle.adapter_identifier,SHAOracle.context_hash,SHAOracle.joint_context_hash]

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
