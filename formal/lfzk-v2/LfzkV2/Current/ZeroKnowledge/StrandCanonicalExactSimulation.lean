import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Exact Ghost-to-Simulator equivalence through one joint change of prover coins. Oracle values, complete proofs, failure outcomes and observer traces are preserved. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalExactSimulation
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2 LigeroFamily
open StrandCanonicalExperiments
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

local notation "Ghost" => ghost binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after
local notation "Simulate" => simulate binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata roundSampler batchingSamples before requestOf after

/-- The triangular joint coin change, with the oracle table and all nonce/label coordinates fixed. -/
def simulationEquiv (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1)))) :
    (HonestCoins × OracleCoins) ≃ (PublicCoins × OracleCoins) :=
    Equiv.prodCongrLeft fun oracleCoins : OracleCoins =>
      let SHA := Lift outside oracleCoins.2.1
      let earlier := before.run SHA
      StrandCanonicalFullCoupling.coupling binary prime primePlan binaryNodes scalars inputFits privateFits setup
        metadata (fun _ => original earlier.1) (fun _ => remaining earlier.1) roundSampler batchingSamples SHA (requestOf earlier.1)
        (StrandGhostMerkle.Tree.labels Codec SHA oracleCoins.2.2 1)
        pivotOne primitive (valid oracleCoins.2.1) (signature oracleCoins.2.1)

local notation "SimulationEquiv" => simulationEquiv binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf

/-- Pointwise equality after changing only prover coins. This includes the guard and every failure outcome. -/
theorem ghost_simulator_view (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1))))
    (coin : HonestCoins × OracleCoins) :
    Ghost outside coin =
      Simulate outside (SimulationEquiv outside pivotOne primitive valid signature coin) := by
  exact (StrandCanonicalFullCoupling.complete_view binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata (fun _ => original (before.run (Lift outside coin.2.2.1)).1)
      (fun _ => remaining (before.run (Lift outside coin.2.2.1)).1)
      roundSampler batchingSamples (Lift outside coin.2.2.1)
    (requestOf (before.run (Lift outside coin.2.2.1)).1)
    (StrandGhostMerkle.Tree.labels Codec (Lift outside coin.2.2.1) coin.2.2.2 1)
    (before.run (Lift outside coin.2.2.1)).1 (before.run (Lift outside coin.2.2.1)).2
    (after (before.run (Lift outside coin.2.2.1)).1) coin.2.2.2 coin.2.1
    pivotOne primitive (valid coin.2.2.1) (signature coin.2.2.1) coin.1).symm


/-- The ghost and witness-free simulator have exactly the same complete-view distribution. -/
theorem ghost_sameDistribution (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1)))) :
    LigeroFamily.SameDistribution (Ghost outside) (Simulate outside) := by
  apply LigeroFamily.sameDistribution_of_equiv (SimulationEquiv outside pivotOne primitive valid signature)
  intro coin
  exact ghost_simulator_view binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original remaining roundSampler batchingSamples before requestOf after outside pivotOne primitive valid signature coin

/-- Compatibility form of the exact ghost equivalence for statistical composition. -/
theorem exact_simulation (outside : Strand.Oracle) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ table : LeafInput → Digest, MdocWitness.UniformHashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1))
      (original ((before.run (Lift outside table)).1)))
    (signature : ∀ table : LeafInput → Digest,
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run (Lift outside table)).1)
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount (requestOf (before.run (Lift outside table)).1)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original ((before.run (Lift outside table)).1)) (remaining ((before.run (Lift outside table)).1)))) :
    StatClose 0 (Ghost outside) (Simulate outside) := by
  apply statClose_zero_of_equiv (SimulationEquiv outside pivotOne primitive valid signature)
  intro coin
  exact ghost_simulator_view binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original remaining roundSampler batchingSamples before requestOf after outside pivotOne primitive valid signature coin

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalExactSimulation

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalExactSimulation (simulationEquiv ghost_simulator_view ghost_sameDistribution exact_simulation)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
