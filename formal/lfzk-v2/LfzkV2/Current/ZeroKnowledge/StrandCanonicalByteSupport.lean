import LfzkV2.Current.ZeroKnowledge.StrandMerkleWindow
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalOracleSupport

/-! Fixed all-branch raw support for both complete canonical views. No
private-state finiteness, execution certificate, or selected-run window is
assumed. All geometry and field values remain those of the runtime model. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteSupport
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

local notation "RuntimePoint" => QueryRuntime.Runtime.Point Repr Sh setup binary.nPublic
local notation "History" => (StrandRuntime.history
  (ProofBodyCodec.codec Repr (MdocRuntime.geometry binary.description prime binary.plan primePlan)) :
  RuntimePoint → Strand.History)
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh
local instance requestFintype : Fintype (CanonicalRuntime.Request binary.description Sh) := by
  apply Fintype.ofInjective (fun request : CanonicalRuntime.Request binary.description Sh =>
    (request.session,request.publicBits,request.primeInputs))
  intro first second same
  cases first
  cases second
  cases same
  rfl
local instance pointFintype : Fintype RuntimePoint := inferInstance
local instance outputFintype : Fintype (Option Output) := inferInstance
attribute [local instance] StrandCanonicalHiding.columnFintype

local notation "ReadWindow" => StrandReadWindow.window History
local notation "MerkleWindow" => StrandMerkleWindow.window Codec 2443
local notation "ObserverWindow" => StrandObserverWindow.window before after

-- Treat the three finite supports through their membership interfaces.
-- Expanding their enumerations is irrelevant to agreement on their union.
attribute [local irreducible] StrandReadWindow.window StrandMerkleWindow.window StrandObserverWindow.window

def window : Finset Bytes := ReadWindow ∪ (MerkleWindow ∪ ObserverWindow)

local notation "Window" => window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after

theorem reads_of_window (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw) :
    @StrandReadWindow.Agree RuntimePoint History first second :=
  StrandReadWindow.agree_of_window History first second
    (fun raw member => same raw (Finset.mem_union_left _ member))

theorem merkle_of_window (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw) :
    ∀ raw ∈ MerkleWindow, first raw = second raw := by
  intro raw member
  apply same raw
  change raw ∈ ReadWindow ∪ (MerkleWindow ∪ ObserverWindow)
  simp only [Finset.mem_union]
  exact Or.inr (Or.inl member)

theorem observer_of_window (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw) :
    ∀ raw ∈ ObserverWindow, first raw = second raw := by
  intro raw member
  apply same raw
  change raw ∈ ReadWindow ∪ (MerkleWindow ∪ ObserverWindow)
  simp only [Finset.mem_union]
  exact Or.inr (Or.inr member)

local notation "Front" => StrandCanonicalHiding.frontend binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler
local notation "Response" => StrandCanonicalHiding.response binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples
local notation "Columns" => StrandCanonicalHiding.columns binary prime primePlan binaryNodes scalars inputFits privateFits setup
  original remaining requestOf
local notation "Stage" => StrandCanonicalHiding.stage binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples requestOf after
local notation "Prepare" => StrandCanonicalBackend.prepare binary.description prime binaryNodes ConcreteSetup.primeNodes
  Repr Sh setup Public bCount metadata roundSampler

omit [DecidableEq B] in
theorem frontend_reads (coins : FrontendCoins) (context : Context) (request : Request) (root : Digest) (first second : Strand.Oracle)
    (reads : @StrandReadWindow.Agree RuntimePoint History first second) :
    Front coins context request root first = Front coins context request root second :=
  congrArg (fun logical => FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata (fun _ => original context) (fun _ => remaining context) logical coins request root)
    (StrandReadWindow.Agree.oracle History roundSampler (Public).fallback reads)

theorem response_reads (coins : HonestCoins) (context : Context) (request : Request) (root : Digest) (first second : Strand.Oracle)
    (reads : @StrandReadWindow.Agree RuntimePoint History first second) :
    Response coins context request root first = Response coins context request root second := by
  have front := frontend_reads binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler coins.1 context request root first second reads
  exact (congrArg (fun value => StrandCanonicalBackend.respondHonest binary.description prime binaryNodes ConcreteSetup.primeNodes
    Repr Sh setup Public bCount pCount metadata roundSampler batchingSamples request value first
    (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits (fun _ => original context) (fun _ => remaining context) coins.1 request) coins.2) front).trans
    (StrandCanonicalBackend.respondHonest_congr_reads binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount pCount metadata roundSampler batchingSamples request _ first second _ _ reads)

theorem stage_reads (coins : HonestCoins) (context : Context) (root : Digest) (first second : Strand.Oracle)
    (reads : @StrandReadWindow.Agree RuntimePoint History first second) :
    Stage coins context (fun raw => first raw.val) root = Stage coins context (fun raw => second raw.val) root := by
  have front := frontend_reads binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler coins.1 context (requestOf context) root first second reads
  have back := response_reads binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples coins context (requestOf context) root first second reads
  have prepared := (congrArg₂ (fun front back => Prepare (requestOf context) front back first (after context)) front back).trans
    (StrandCanonicalBackend.prepare_oracle_congr_reads binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount metadata roundSampler (requestOf context) _ _ first second (after context) reads)
  exact (StrandCanonicalHiding.stage_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples requestOf after coins context first root).trans
    (prepared.trans (StrandCanonicalHiding.stage_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata
      original remaining roundSampler batchingSamples requestOf after coins context second root).symm)

/-- All post-proof branches are covered at every context reachable before
proof generation, including branches selected by a programmed leaf answer. -/
theorem later_of_window (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw)
    (context : Context) (reachable : context ∈ StrandObserverWindow.outputs before) :
    ∀ output, ∀ raw ∈ OracleWindow.queries (after context output), first raw = second raw := by
  intro output raw member
  exact observer_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after
    first second same raw (StrandObserverWindow.after_subset before after context reachable output member)

/-- The honest experiment depends only on the fixed all-branch support.
In particular, the support is not chosen after the proof or oracle is seen. -/
theorem rawReal_congr (coins : HonestCoins × ((Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)))
    (first second : Strand.Oracle) (same : ∀ raw ∈ Window, first raw = second raw) :
    StrandCanonicalHiding.rawReal binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata original remaining roundSampler batchingSamples before requestOf after coins first =
      StrandCanonicalHiding.rawReal binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata original remaining roundSampler batchingSamples before requestOf after coins second := by
  have reads := reads_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after
    first second same
  have merkle := merkle_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after
    first second same
  have earlier := StrandObserverWindow.before_congr before after first second
    (observer_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after first second same)
  have root := StrandMerkleWindow.commitLabels_congr Codec 2443 first second merkle
    (fun index => (index,coins.2.1 index)) (Columns coins.1 (before.run second).1) 1
  dsimp only [StrandCanonicalHiding.rawReal,StrandGhostMerkle.Schedule.honest]
  rw [earlier]
  rw [root,stage_reads binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples requestOf after coins.1 (before.run second).1 _ first second reads]
  rw [StrandMerkleWindow.openCore_congr Codec 2443 first second merkle]
  apply congrArg (fun result => (before.run second,result))
  rw [StrandCanonicalHiding.stage_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples requestOf after coins.1 (before.run second).1 second]
  exact StrandCanonicalBackend.prepare_run_congr binary.description prime binaryNodes ConcreteSetup.primeNodes
    Repr Sh setup Public bCount metadata roundSampler _ _ _ second first second (after (before.run second).1)
    (later_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after first second same
      (before.run second).1 (StrandObserverWindow.output_mem before second)) _ _

/-- The public simulator has the same finite support. Leaf programming
preserves agreement on every protocol read and every later observer query. -/
theorem rawSimulate_congr (coins : PublicCoins × ((Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)))
    (first second : Strand.Oracle) (same : ∀ raw ∈ Window, first raw = second raw) :
    StrandCanonicalHiding.rawSimulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata roundSampler batchingSamples before requestOf after coins first =
      StrandCanonicalHiding.rawSimulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata roundSampler batchingSamples before requestOf after coins second := by
  have reads := reads_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after
    first second same
  have merkle := merkle_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after
    first second same
  have nodes := fun index within children => merkle _ (StrandMerkleWindow.node_mem Codec 2443 index within children)
  have earlier := StrandObserverWindow.before_congr before after first second
    (observer_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after first second same)
  have root := StrandGhostMerkle.Tree.labels_congr Codec first second nodes coins.2.2 1
  dsimp only [StrandCanonicalHiding.rawSimulate]
  rw [earlier,root]
  dsimp only [StrandCanonicalFullCoupling.simulatedView,StrandCanonicalFullCoupling.actualOracle]
  rw [StrandCanonicalBackend.logicalOracle_congr_reads binary.description Repr Sh setup roundSampler (Public).fallback
    first second reads]
  rw [StrandCanonicalBackend.respond_congr_reads binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount pCount metadata roundSampler batchingSamples _ _ first second coins.1.2 reads]
  exact StrandCanonicalBackend.fullView_congr_reads binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount metadata roundSampler _ _ _ first second _ _ (after (before.run second).1) coins.2.2 coins.2.1 reads nodes
    (later_of_window binary prime primePlan binaryNodes scalars inputFits privateFits setup before after first second same
      (before.run second).1 (StrandObserverWindow.output_mem before second))

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteSupport
