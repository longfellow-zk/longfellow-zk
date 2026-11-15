import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteSupport

/-! The fixed raw byte-oracle support of the canonical privacy game. Both
experiments, including the simulator's opened-leaf-only programming, are
independent of every coordinate outside it. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteOracle
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)
variable (setup : MdocRuntime.FormatSetup)
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "bCount" => RuntimeStatement.binary_count binary prime primePlan inputFits privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "FrontendCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BackendCoins" => Backend.JointMasks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => StrandCanonicalContext.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
variable (metadata : Format.RequestMetadata (MdocRuntime.format binary.description prime binary.plan primePlan scalars inputFits privateFits (RuntimeStatement.degreeFits binary) setup) (MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes))
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (original : Context → Fin binary.nPrivate → Bool)
variable (remaining : Context → Fin prime.remaining → N)
variable {blocks : ℕ}
variable (roundSampler : Format.Point (MdocRuntime.format binary.description prime binary.plan primePlan scalars inputFits privateFits (RuntimeStatement.degreeFits binary) setup) →
    Merkle.RandomOracle.Tree Strand.Word Strand.Digest
      (Option (MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)) blocks)
variable (batchingSamples : MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes →
  RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes
    (MdocRuntime.format binary.description prime binary.plan primePlan scalars inputFits privateFits (RuntimeStatement.degreeFits binary) setup)
    (StrandCanonicalContext.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))

local notation "Fmt" => MdocRuntime.format binary.description prime binary.plan primePlan scalars inputFits privateFits (RuntimeStatement.degreeFits binary) setup
local notation "Codec" => StrandCanonicalBackend.indexedCodec binary.description prime binaryNodes
  ConcreteSetup.primeNodes (Fmt) Public
local notation "Dec" => StrandCanonicalBackend.indexedDecoders binary.description prime binaryNodes
  ConcreteSetup.primeNodes (Fmt) Public
local notation "Column" => StrandCanonicalBackend.Leaf binary.description prime binaryNodes
  ConcreteSetup.primeNodes (Fmt) Public
local notation "HonestCoins" => FrontendCoins × BackendCoins
local notation "PublicCoins" => CompleteSimulation.Coins binary prime × BackendCoins

variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)

attribute [local instance] StrandCanonicalHiding.columnFintype
  StrandCanonicalHiding.honestCoinsFintype StrandCanonicalHiding.publicCoinsFintype
local notation "AuxiliaryCoins" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "LeafInput" => (Fin 2443 × MerkleNonce) × Column
local notation "PublicView" => Protocol.Execution.PublicView Context (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) Observed
local notation "RawReal" => StrandCanonicalExecution.rawReal binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "RawSimulate" => StrandCanonicalExperiments.rawSimulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata roundSampler batchingSamples before requestOf after
local notation "Leaves" => StrandCanonicalHiding.leafWindow binary prime primePlan binaryNodes scalars inputFits privateFits setup
attribute [local irreducible] StrandCanonicalByteSupport.window

/-- A fixed support containing every protocol and observer query in either
experiment. It depends only on public configuration and observer programs,
never on a witness, sampled oracle, or selected execution. -/
def window : Finset Bytes := Leaves ∪
  StrandCanonicalByteSupport.window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after

local notation "Window" => window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after

/-- The complete real view is independent of all coordinates outside the
derived support, including its prior and subsequent query/answer traces. -/
theorem real_extend (coins : HonestCoins × AuxiliaryCoins) (SHA outside : Strand.Oracle) :
    RawReal coins (OracleWindow.extend Window (fun raw => SHA raw.val) outside) = RawReal coins SHA := by
  apply StrandCanonicalByteSupport.rawReal_congr binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples before requestOf after coins _ SHA
  intro raw member
  apply OracleWindow.extend_mem Window (fun raw => SHA raw.val) outside raw
  change raw ∈ Leaves ∪ _
  simp only [Finset.mem_union]
  exact Or.inr member

/-- Opened-leaf programming does not introduce an outside-support
observable dependency into the simulator. This also covers failure views. -/
theorem simulate_extend (coins : PublicCoins × AuxiliaryCoins) (SHA outside : Strand.Oracle) :
    RawSimulate coins (OracleWindow.extend Window (fun raw => SHA raw.val) outside) = RawSimulate coins SHA := by
  apply StrandCanonicalByteSupport.rawSimulate_congr binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata roundSampler batchingSamples before requestOf after coins _ SHA
  intro raw member
  apply OracleWindow.extend_mem Window (fun raw => SHA raw.val) outside raw
  change raw ∈ Leaves ∪ _
  simp only [Finset.mem_union]
  exact Or.inr member

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteOracle
