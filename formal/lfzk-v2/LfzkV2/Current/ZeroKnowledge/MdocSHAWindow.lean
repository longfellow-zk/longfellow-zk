import LfzkV2.Current.ZeroKnowledge.MdocPublicSetup
import LfzkV2.Current.ZeroKnowledge.MerkleRuntime

/-! The concrete mdoc Merkle codec varies with just one public digest.
Its field maps and physical row layout are fixed by the runtime constructor.
Taking the union over every digest therefore gives one finite family of
codec inputs before the complementary SHA slice chooses its context. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocSHAWindow
open Application ApplicationSetup ConcreteSetup RecursivePolygero
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

def binaryParticipant :=
  let geometry := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan
  ((backend (ConcreteSetup.binaryNodes cantor) binary.description.cells).indexed (geometry.affineRows .binary)).participant

def primeParticipant :=
  let geometry := MdocRuntime.geometry binary.description prime.description binary.plan prime.plan
  ((backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.description.remaining prime.description.pads)).indexed
    (geometry.affineRows .prime)).participant

local notation "First" => binaryParticipant binary prime cantor
local notation "Second" => primeParticipant binary prime

/-- Physical row widths are fixed independently of transcript callbacks. -/
abbrev Leaf :=
  MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
    MerkleCompiler.Leaf (ZMod Current.Adapter.Mdoc.primeOrder)
      (rows (CellLayout.Prime.cells prime.description.remaining prime.description.pads)) 0

/-- The Merkle layout needs only the two fixed backend participants, their
field representations and a context digest. It does not inspect transcript
sampling, public setup hashes or the runtime's other callbacks. -/
def codec (context : Digest) : Merkle.MH.Codec (Fin 2443 × MerkleNonce) (Leaf binary prime) Digest Bytes :=
  MerkleRuntime.codec First Second (MdocRuntime.representations scalars)
    (Equiv.refl B) (Equiv.refl (ZMod Current.Adapter.Mdoc.primeOrder)) context (by decide)

/-- This boundary is checked once against the literal runtime constructor.
Higher-level window proofs can then use the static codec without unfolding
the complete verifier configuration. -/
def runtimeCodec (SHA : Bytes → Digest) : Merkle.MH.Codec (Fin 2443 × MerkleNonce) (Leaf binary prime) Digest Bytes :=
  let nodes := ConcreteSetup.binaryNodes cantor
  let P := backend nodes binary.description.cells
  let R := backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
  let repr := MdocRuntime.representations scalars
  let shape := MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)
  let setup := MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
  let cfg := MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA
  let publicCfg := CompleteCanonicalVerifier.publicConfig binary.description prime.description nodes ConcreteSetup.primeNodes
    repr shape setup cfg
  MerkleRuntime.codec (RuntimeVerifier.first binary.description prime.description P R publicCfg).participant
    (RuntimeVerifier.second binary.description prime.description P R publicCfg).participant
    repr cfg.binaryField cfg.primeField setup.jointContext (by decide)

theorem runtime_codec (SHA : Bytes → Digest) :
    runtimeCodec binary prime cantor scalars ids bounds SHA =
    codec binary prime cantor scalars (MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA).jointContext := rfl

theorem leaf_domain (context : Digest) (value) :
    SHAOracle.merkleDomain ((codec binary prime cantor scalars context).leafEnc value) :=
  SHAOracle.leaf_in_domain First Second (MdocRuntime.representations scalars)
    (Equiv.refl B) (Equiv.refl (ZMod Current.Adapter.Mdoc.primeOrder))
    context (by decide) (value.1,MerkleRuntime.tupleLeaf First Second value.2)

theorem node_domain (context : Digest) (value) :
    SHAOracle.merkleDomain ((codec binary prime cantor scalars context).nodeEnc value) :=
  SHAOracle.node_in_domain First Second (MdocRuntime.representations scalars)
    (Equiv.refl B) (Equiv.refl (ZMod Current.Adapter.Mdoc.primeOrder))
    context (by decide) value

end LfzkV2.Current.ZeroKnowledge.MdocSHAWindow
