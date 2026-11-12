import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalRows
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalSchedule

/-! Actual honest execution: columns precede the root, numbered challenge reads follow it, and rawReal retains the whole observer view. Completeness imports this module without importing privacy. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
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
local notation "bCount" => RuntimeStatement.binary_count binary prime primePlan inputFits privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "FrontendCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BackendCoins" => CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => StrandCanonicalFullCoupling.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (original : Context → Fin binary.nPrivate → Bool)
variable (remaining : Context → Fin prime.remaining → N)
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
local notation "ToLeaf" => StrandCanonicalBackend.leafEquiv binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "HonestCoins" => FrontendCoins × BackendCoins

variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)

def columns (coins : HonestCoins) (context : Context) : Fin 2443 → Column :=
  let cells := FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
    (fun _ => original context) (fun _ => remaining context) coins.1
    (requestOf context)
  fun index => ToLeaf (StrandCanonicalBackend.committedColumns binary.description prime binaryNodes
    ConcreteSetup.primeNodes cells coins.2 index)

def frontend (coins : FrontendCoins) (context : Context) (request : Request) (root : Digest) (SHA : Strand.Oracle) :=
  FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata (fun _ => original context) (fun _ => remaining context)
    (StrandCanonicalFullCoupling.actualOracle binary prime primePlan binaryNodes scalars inputFits privateFits setup
      roundSampler SHA) coins request root

local notation "Front" => frontend binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler

def response (coins : HonestCoins) (context : Context) (request : Request) (root : Digest) (SHA : Strand.Oracle) :=
  StrandCanonicalBackend.respondHonest binary.description prime binaryNodes ConcreteSetup.primeNodes
    Repr Sh setup Public bCount pCount metadata roundSampler batchingSamples request (Front coins.1 context request root SHA) SHA
    (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
      (fun _ => original context) (fun _ => remaining context) coins.1 request) coins.2

local notation "Response" => response binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples
local notation "OtherOracle" => StrandCanonicalBackend.nonleafOracle binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "Prepare" => StrandCanonicalBackend.prepare binary.description prime binaryNodes ConcreteSetup.primeNodes
  Repr Sh setup Public bCount metadata roundSampler

omit [DecidableEq B] in
theorem frontend_congr (coins : FrontendCoins) (context : Context) (request : Request) (root : Digest) (first second : Strand.Oracle)
    (agree : ∀ input : Strand.Input, first input.encode = second input.encode) :
    Front coins context request root first = Front coins context request root second := by
  exact congrArg (fun logical => FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars
    inputFits privateFits setup metadata (fun _ => original context) (fun _ => remaining context) logical coins request root)
    (StrandCanonicalBackend.logicalOracle_congr binary.description Repr Sh setup roundSampler
      (Public).fallback first second agree)

theorem response_congr (coins : HonestCoins) (context : Context) (request : Request) (root : Digest) (first second : Strand.Oracle)
    (agree : ∀ input : Strand.Input, first input.encode = second input.encode) :
    Response coins context request root first = Response coins context request root second := by
  have front := frontend_congr binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata
    original remaining roundSampler coins.1 context request root first second agree
  exact (congrArg (fun value => StrandCanonicalBackend.respondHonest binary.description prime binaryNodes
    ConcreteSetup.primeNodes Repr Sh setup Public bCount pCount metadata roundSampler batchingSamples request value first
      (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
        (fun _ => original context) (fun _ => remaining context) coins.1 request) coins.2)
    front).trans
    (StrandCanonicalBackend.respondHonest_congr binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount pCount metadata roundSampler batchingSamples request _ first second _ _ agree)

def stage (coins : HonestCoins) (context : Context)
    (read : StrandGhostMerkle.Observer.Other Codec Dec → Digest) (root : Digest) :
    StrandGhostMerkle.Schedule.Prepared 2443 MerkleNonce Column Digest Bytes
      (Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) × Observed) postQueries :=
  let SHA := OtherOracle read
  Prepare (requestOf context) (Front coins.1 context (requestOf context) root SHA)
    (Response coins context (requestOf context) root SHA) SHA (after context)

local notation "Stage" => stage binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples requestOf after
local notation "Columns" => columns binary prime primePlan binaryNodes scalars inputFits privateFits setup
  original remaining requestOf

/-- The nonce-independent stage uses exactly the real oracle at every
numbered strand address; dummy leaf answers are never inspected. -/
theorem stage_eq (coins : HonestCoins) (context : Context) (SHA : Strand.Oracle) (root : Digest) :
    Stage coins context (fun raw => SHA raw.val) root =
      Prepare (requestOf context) (Front coins.1 context (requestOf context) root SHA)
        (Response coins context (requestOf context) root SHA) SHA (after context) := by
  have agree := StrandCanonicalBackend.nonleafOracle_agree binary.description prime binaryNodes
    ConcreteSetup.primeNodes Repr Sh setup Public SHA
  have front := frontend_congr binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler coins.1 context (requestOf context) root _ SHA agree
  have back := response_congr binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples coins context (requestOf context) root _ SHA agree
  exact (congrArg₂ (fun front back => Prepare (requestOf context) front back
    (OtherOracle (fun raw => SHA raw.val)) (after context)) front back).trans
    (StrandCanonicalBackend.prepare_oracle_congr binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount metadata roundSampler (requestOf context) _ _ _ SHA (after context) agree)

local notation "AuxiliaryCoins" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "PublicView" => Protocol.Execution.PublicView Context (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) Observed

/-- The byte-oracle experiment receives one oracle. The auxiliary labels
are unused on the real side, and make no change to its distribution. -/
def rawReal (coin : HonestCoins × AuxiliaryCoins) (SHA : Strand.Oracle) : PublicView :=
  StrandGhostMerkle.Schedule.honest Codec Dec before (Columns coin.1) (Stage coin.1) SHA coin.2.1


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution (columns frontend response frontend_congr response_congr stage stage_eq rawReal)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
