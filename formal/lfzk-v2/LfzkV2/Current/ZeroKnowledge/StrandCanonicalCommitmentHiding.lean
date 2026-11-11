import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSlice

/-! The statistical Real-to-Ghost hop. The analysis swaps all actual leaf addresses; the guarded ghost installs only disclosed leaves. No algebraic coin-change proof is imported. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
open StrandCanonicalExecution StrandCanonicalExperiments
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
local notation "ToLeaf" => StrandCanonicalBackend.leafEquiv binary.description prime binaryNodes
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

local notation "Front" => frontend binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler
local notation "Response" => response binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples
local notation "Stage" => stage binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples requestOf after
local notation "Columns" => columns binary prime primePlan binaryNodes scalars inputFits privateFits setup
  original remaining requestOf

local notation "OracleCoins" => StrandGhostMerkle.Probability.Coins 2443 MerkleNonce
  ((Fin 2443 × MerkleNonce) × Column) Digest
local notation "Lift" => StrandGhostMerkle.Swap.Slice.oracle
  (StrandGhostMerkle.Probability.leafEmbedding Codec Dec)

local instance columnFintype : Fintype Column :=
  Fintype.ofEquiv (StrandCanonicalBackend.PhysicalColumn binary.description prime) ToLeaf
local instance honestCoinsFintype : Fintype HonestCoins := Fintype.ofFinite _
local instance publicCoinsFintype : Fintype PublicCoins := Fintype.ofFinite _

local notation "Real" => real binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "Ghost" => ghost binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after

local notation "Disclosed" => StrandCanonicalBackend.disclosed binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public bCount metadata roundSampler
local notation "Abort" => fun context => Merkle.RandomOracle.Tree.map (after context none)
  (fun observed => (none,observed))

/-- The generic hiding experiment is the concrete ghost-commitment view
already used by the exact frontend/backend coupling. -/
theorem ghost_eq (coins : HonestCoins) (SHA : Strand.Oracle)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce) :
    StrandGhostMerkle.Schedule.simulate Codec Dec before (Columns coins) (Stage coins) Abort SHA leaves
        (fun index => nonces index.val) =
      StrandCanonicalFullCoupling.honestView binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata original remaining roundSampler batchingSamples SHA (requestOf (before.run SHA).1)
        (StrandGhostMerkle.Tree.labels Codec SHA leaves 1) (before.run SHA).1 (before.run SHA).2
        (after (before.run SHA).1) leaves nonces coins := by
  let context := (before.run SHA).1
  let root := StrandGhostMerkle.Tree.labels Codec SHA leaves 1
  have restricted : Disclosed (requestOf context) (Front coins.1 (requestOf context) root SHA)
      (Response coins (requestOf context) root SHA) SHA (after context) =
      fun index => Columns coins context index.val := by
    exact StrandCanonicalBackend.disclosed_respondHonest binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount metadata roundSampler pCount batchingSamples (requestOf context)
      (Front coins.1 (requestOf context) root SHA) SHA
      (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits original remaining coins.1
        (requestOf context)) coins.2 (after context)
  dsimp only [StrandGhostMerkle.Schedule.simulate,StrandGhostMerkle.Schedule.prepared]
  rw [stage_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples requestOf after coins (before.run SHA).1 SHA
    (StrandGhostMerkle.Tree.labels Codec SHA leaves 1)]
  rw [← restricted]
  exact StrandCanonicalBackend.complete_prepared binary.description prime binaryNodes ConcreteSetup.primeNodes
    Repr Sh setup Public bCount metadata roundSampler (requestOf context)
    (Front coins.1 (requestOf context) root SHA) (Response coins (requestOf context) root SHA)
    SHA context (before.run SHA).2 (after context) leaves nonces

/-- One statistical hop, with both complete raw observer traces retained.
The fresh nonce space has 256 bits; there is no factor for column count and
no transcript programming or digest-collision assumption. -/
theorem commitment_hiding (outside : Strand.Oracle) :
    StatClose ((preQueries + postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ))
      (Real outside) (Ghost outside) := by
  have nonnegative : (0 : ℚ) ≤ (preQueries + postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ) :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have separated : ∀ index children salt message, (Codec).nodeEnc index children ≠ (Codec).leafEnc (salt,message) := by
    intro index children salt message
    exact Ne.symm (MerkleWireCodec.role_ranges_disjoint _ _ _ _ _ _ _ index (salt,message) children)
  have mixed := statClose_mix nonnegative
    (fun coins : HonestCoins => fun oracleCoins : OracleCoins =>
      StrandGhostMerkle.Schedule.honest Codec Dec before (Columns coins) (Stage coins)
        (Lift outside oracleCoins.2.1) oracleCoins.1)
    (fun coins : HonestCoins => fun oracleCoins : OracleCoins =>
      StrandGhostMerkle.Schedule.simulate Codec Dec before (Columns coins) (Stage coins) Abort
        (Lift outside oracleCoins.2.1) oracleCoins.2.2 (fun index => oracleCoins.1 index.val))
    (fun coins => Probability.changeFintype (StrandGhostMerkle.Probability.statistical_hiding_slice
      (Salt := MerkleNonce) (Message := Column) (Digest := Digest) (Raw := Bytes) Codec Dec before
      (Columns coins) (Stage coins) Abort separated outside))
  apply statClose_reindex (Equiv.refl (HonestCoins × OracleCoins))
    (Equiv.refl (HonestCoins × OracleCoins)) (fun _ => rfl) _ mixed
  intro coin
  exact (ghost_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples before requestOf after coin.1 (Lift outside coin.2.2.1) coin.2.2.2 coin.2.1).symm


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding (ghost_eq commitment_hiding)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
