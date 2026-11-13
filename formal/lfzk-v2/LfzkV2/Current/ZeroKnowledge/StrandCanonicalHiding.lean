import LfzkV2.Current.ZeroKnowledge.StrandCanonicalCommitmentHiding
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExactSimulation
import LfzkV2.Current.ZeroKnowledge.StrandLeafWindow

/-! Privacy assembly: Real is statistically close to Ghost, which is exactly distributed as the public simulator. The only error is indexed nonce guessing; raw-oracle averaging follows the two-hop composition. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
open StrandCanonicalExecution StrandCanonicalExperiments
open StrandCanonicalCommitmentHiding StrandCanonicalExactSimulation
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
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "FrontendCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BackendCoins" => Backend.JointMasks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => StrandCanonicalContext.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
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
    (StrandCanonicalContext.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))

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

variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)

local notation "OracleCoins" => StrandGhostMerkle.Probability.Coins 2443 MerkleNonce
  ((Fin 2443 × MerkleNonce) × Column) Digest
local notation "Lift" => StrandGhostMerkle.Swap.Slice.oracle
  (StrandGhostMerkle.Probability.leafEmbedding Codec Dec)
local notation "LeafInput" => (Fin 2443 × MerkleNonce) × Column

local instance columnFintype : Fintype Column :=
  Fintype.ofEquiv (StrandCanonicalBackend.PhysicalColumn binary.description prime) ToLeaf
local instance honestCoinsFintype : Fintype HonestCoins := Fintype.ofFinite _
local instance publicCoinsFintype : Fintype PublicCoins := Fintype.ofFinite _

local notation "Real" => real binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "Ghost" => ghost binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "Simulate" => simulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata roundSampler batchingSamples before requestOf after

/-- Complete canonical-view privacy in the fixed-configuration leaf-oracle
game. Witness validity derives the backend truth needed by the exact coin
change; callers supply no execution or simulation certificate. The only
statistical loss is guessing a fresh committed nonce in the prior/later view. -/
theorem statClose (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1)))) :
    StatClose ((preQueries + postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ))
      (Real outside) (Simulate outside) := by
  have commitmentLaw := commitment_hiding binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples before requestOf after outside
  have exactView := exact_simulation binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples before requestOf after outside pivotOne primitive valid signature
  simpa only [add_zero] using commitmentLaw.trans exactView

local notation "AuxiliaryCoins" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)

local notation "RawReal" => rawReal binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "RawSimulate" => rawSimulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata roundSampler batchingSamples before requestOf after

def leafWindow : Finset Bytes :=
  StrandLeafWindow.window (StrandGhostMerkle.Probability.leafEmbedding Codec Dec)


theorem raw_fixedComplement (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1)))) :
    StatClose ((preQueries + postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ))
      (fun coin : (HonestCoins × AuxiliaryCoins) × (LeafInput → Digest) => RawReal coin.1 (Lift outside coin.2))
      (fun coin : (PublicCoins × AuxiliaryCoins) × (LeafInput → Digest) => RawSimulate coin.1 (Lift outside coin.2)) := by
  let exchange (R : Type) : ((R × AuxiliaryCoins) × (LeafInput → Digest)) ≃ R × OracleCoins :=
    { toFun := fun coin => (coin.1.1,coin.1.2.1,coin.2,coin.1.2.2)
      invFun := fun coin => ((coin.1,coin.2.1,coin.2.2.2),coin.2.2.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Probability.changeFintype (statClose_reindex (exchange HonestCoins) (exchange PublicCoins)
    (fun _ => rfl) (fun _ => rfl)
    (statClose binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
      roundSampler batchingSamples before requestOf after outside pivotOne primitive valid signature))


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
