import LfzkV2.Current.MdocRuntime
import LfzkV2.Current.MetadataIdentifiers

/-! Exact setup values for the current mdoc verifier. The trusted statement
constants and the identifier hash are inputs; the statement message's head
and the generated adapter fragment identifier are constructed here, and the
statement binds that identifier in its own `Circuit` message, as Rust does.
The fragment hash is an ordinary auxiliary hash input, not an additional
transcript query. The Merkle hash domain is a protocol constant
(`MerkleWireCodec.hashDomain`), so the setup computes no context. -/
noncomputable section
set_option maxRecDepth 4096
namespace LfzkV2.Current.MdocIdentifiers
open Application ApplicationSetup
open CanonicalPrefix (utf8)
open TranscriptV2.Framing (encodeLE)
open scoped Classical

/-- The statement constants after the combined hash, as node 0 absorbs them:
the statement message's (version, attribute count) value, then the `Circuit`
messages of the hash circuit, the adapter fragment and the signature circuit,
then the `CommitmentLayout`, `AdapterLayout` and `JointGeometry` messages.
The fragment's identifier is computed from the hash circuit's shape
(`fragmentId`); the other constants are fixed by the trusted circuits and
supplied around it. Each `Circuit` message is the 32-byte circuit ID alone,
which hashes the circuit's shape. Each `CommitmentLayout` has five values:
the cell counts, the packing descriptor, the native storage runs as (first,
count, cell) triples, the bit-stored runs as (first, count, start, width)
quadruples, each list in increasing first value and both empty for a native
participant, and the mask's (start, width). The Polygero profile is in
`JointGeometry` only.

The fixed bytes and the composed constants equal the Rust encoding by the
golden tests (`Tests/TaggedFormat`). The model does not derive the fixed
bytes from the setup, so Lean does not prove that they determine the
circuits, layouts and geometry the verifier uses (transcript I3). -/
structure Identifiers where
  combinedHash : Digest
  /-- The statement value, then the hash circuit's `Circuit` message. -/
  beforeFragment : Bytes
  /-- The signature circuit's `Circuit` message and the layout and geometry
  messages. -/
  afterFragment : Bytes
  hash : Bytes → Digest

def binaryField : Bytes := utf8 "GF2[x]/(x^128+x^7+x^2+x+1)/polynomial/v1"

def primeField {B : Type} (scalars : MdocRuntime.Scalars B) : Bytes :=
  utf8 "prime/canonical-integer/v1/" ++ scalars.prime.encode (-1)

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)

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

/-- Identifier of the generated adapter fragment, rebuilt from the hash
circuit's shape: its virtual leaves start after the committed inputs. -/
def fragmentId (ids : Identifiers) : Digest :=
  MetadataIdentifiers.fragmentId ids.hash scalars.binary.encode binary.description.shape
    (binary.nPublic+binary.nPrivate+2*(768+256+10)) binary.nPublic (binary.nPublic+binary.nPrivate)

/-- `Circuit`, the tag of a circuit identifier message
(`rust/src/runtime/v2/proto/tags.rs`). -/
def circuitTag : ℕ := 18

/-- The `Circuit` message of a circuit identifier: its tag, then the
identifier as `Bytes(32)`. -/
def circuitMessage (id : Digest) : Bytes :=
  TaggedCodec.word circuitTag ++ TaggedCodec.digestValue.encode id

/-- The statement constants with the adapter fragment identifier `fragment`
in its `Circuit` message. -/
def constants (ids : Identifiers) (fragment : Digest) : Bytes :=
  TaggedCodec.digestValue.encode ids.combinedHash ++ ids.beforeFragment ++ circuitMessage fragment ++
    ids.afterFragment

/-- The `MdocStatement` tag and its protocol value, before the session. -/
def statementHead : Bytes :=
  TaggedCodec.word 16 ++ TaggedCodec.word 0 ++ TaggedCodec.word 32 ++ utf8 "longfellow/v2/mdoc/transcript/v2"

/-- The setup the statement node absorbs for the adapter fragment identifier
`fragment`. It reads no basis and no hash: the Merkle hash domain is a
protocol constant. -/
def setupOf (_cantor : Module.Basis (Fin 128) (ZMod 2) B) (_scalars : MdocRuntime.Scalars B)
    (ids : Identifiers) (_bounds : Bounds binary prime) (fragment : Digest) : MdocRuntime.FormatSetup where
  head := statementHead
  constants := constants ids fragment

/-- The setup the statement node absorbs. Its one hash is the adapter
fragment identifier, which the statement binds; it reads no basis. -/
def setup (_cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
    (ids : Identifiers) (bounds : Bounds binary prime) : MdocRuntime.FormatSetup :=
  setupOf binary prime _cantor scalars ids bounds (fragmentId binary scalars ids)

end LfzkV2.Current.MdocIdentifiers
