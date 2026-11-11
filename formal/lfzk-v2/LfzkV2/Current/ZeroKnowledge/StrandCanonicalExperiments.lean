import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms
import LfzkV2.Current.ZeroKnowledge.StrandLeafOracle

/-! The three complete observer experiments: actual Real, guarded honest Ghost with independent leaf labels, and the witness-free simulator. Both ghost constructions check only disclosed leaf addresses. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
open StrandCanonicalExecution
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)
variable (setup : FingerprintPrefix.Setup)
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "FrontendCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BackendCoins" => CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => StrandCanonicalFullCoupling.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin prime.remaining → N)
variable {blocks : ℕ}
variable (roundSampler : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) setup binary.nPublic →
    Merkle.RandomOracle.Tree Strand.Word Strand.Digest
      (Option (MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)) blocks)
variable (batchingSamples : MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes →
  RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes
    (MdocRuntime.representations scalars)
    (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
      (RuntimeStatement.degreeFits binary)) setup
    (StrandCanonicalFullCoupling.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))

local notation "Codec" => StrandCanonicalBackend.indexedCodec binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "Dec" => StrandCanonicalBackend.indexedDecoders binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "Column" => StrandCanonicalBackend.Leaf binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "HonestCoins" => FrontendCoins × BackendCoins
local notation "PublicCoins" => CompleteSimulation.Coins binary prime × BackendCoins

variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)

local notation "Stage" => stage binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples requestOf after
local notation "Columns" => columns binary prime primePlan binaryNodes scalars inputFits privateFits setup
  original remaining requestOf

local notation "OracleCoins" => StrandGhostMerkle.Probability.Coins 2443 MerkleNonce
  ((Fin 2443 × MerkleNonce) × Column) Digest
local notation "Lift" => StrandGhostMerkle.Swap.Slice.oracle
  (StrandGhostMerkle.Probability.leafEmbedding Codec Dec)

/-- Actual committed columns determine the root before any frontend or
backend challenge. The prepared stage uses the canonical encoder, and the
later observer sees the complete proof and ordinary oracle answers. -/
def real (outside : Strand.Oracle) (coin : HonestCoins × OracleCoins) :=
  StrandGhostMerkle.Schedule.honest Codec Dec before (Columns coin.1) (Stage coin.1)
    (Lift outside coin.2.2.1) coin.2.1

/-- The only intermediate experiment: independent leaf labels replace the
commitment, while frontend and backend still use the honest private coins. -/
def ghost (outside : Strand.Oracle) (coin : HonestCoins × OracleCoins) :=
  let SHA := Lift outside coin.2.2.1
  let earlier := before.run SHA
  StrandCanonicalFullCoupling.honestView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2.2 coin.2.1 coin.1

/-- No witness or honest-cell argument enters the public simulation. Only
disclosed columns are installed, subject to the disclosed-address prior-query guard. -/
def simulate (outside : Strand.Oracle) (coin : PublicCoins × OracleCoins) :=
  let SHA := Lift outside coin.2.2.1
  let earlier := before.run SHA
  StrandCanonicalFullCoupling.simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2.2 coin.2.1 coin.1

local notation "AuxiliaryCoins" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "PublicView" => (Context × List (Bytes × Digest)) ×
  (Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) × Observed) × List (Bytes × Digest)

def rawSimulate (coin : PublicCoins × AuxiliaryCoins) (SHA : Strand.Oracle) : PublicView :=
  let earlier := before.run SHA
  StrandCanonicalFullCoupling.simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2 coin.2.1 coin.1


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments (real ghost simulate rawSimulate)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
