import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalRows
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalView
import LfzkV2.Current.ZeroKnowledge.StrandLeafOracle

noncomputable section

/-! Honest and public constructions of the complete guarded ghost view. These definitions contain no hiding proof. -/
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
open StrandCanonicalContext
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)
variable (setup : FingerprintPrefix.Setup)
local notation "G" => MdocRuntime.geometry binary.description prime binary.plan primePlan
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "bCount" => RuntimeStatement.binary_count binary prime primePlan inputFits privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Point" => QueryRuntime.Runtime.Point Repr Sh setup binary.nPublic
local notation "Answer" => MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes
local notation "FrontendCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BackendCoins" => Backend.JointMasks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (originalWitness : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remainingWitness : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin prime.remaining → N)
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
    (configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))

section Views
variable (SHA : Strand.Oracle)
local notation "H" => actualOracle binary prime primePlan binaryNodes scalars inputFits privateFits setup roundSampler SHA
local notation "honestFront" => FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars
  inputFits privateFits setup metadata originalWitness remainingWitness H
local notation "publicFront" => FrontendCanonicalRows.publicBody binary prime primePlan binaryNodes scalars
  inputFits privateFits setup metadata H

/-- The public simulator takes only public frontend/backend randomness.
Its completion includes the actual canonical body, authentication, final
seal, and the later raw query/answer trace. -/
def simulatedView (request : Request) (root : Digest) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (coins : CompleteSimulation.Coins binary prime × BackendCoins) :=
  let front := publicFront coins.1 request root
  let response := StrandCanonicalBackend.respond (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount pCount metadata roundSampler batchingSamples request front SHA coins.2
  StrandCanonicalBackend.fullView (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount metadata roundSampler request context prior after leaves nonces front response SHA

def honestView (request : Request) (root : Digest) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (coins : FrontendCoins × BackendCoins) :=
  let front := honestFront coins.1 request root
  let cells := FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits originalWitness remainingWitness coins.1 request
  let response := StrandCanonicalBackend.respondHonest (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount pCount metadata roundSampler batchingSamples request front SHA cells coins.2
  StrandCanonicalBackend.fullView (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount metadata roundSampler request context prior after leaves nonces front response SHA

end Views
/-! The three complete observer experiments: actual Real, guarded honest Ghost with independent leaf labels, and the witness-free simulator. Both ghost constructions check only disclosed leaf addresses. -/
open StrandCanonicalExecution LigeroFamily
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
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
  StrandCanonicalExperiments.honestView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata (fun _ => original earlier.1) (fun _ => remaining earlier.1) roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2.2 coin.2.1 coin.1

/-- No witness or honest-cell argument enters the public simulation. Only
disclosed columns are installed, subject to the disclosed-address prior-query guard. -/
def simulate (outside : Strand.Oracle) (coin : PublicCoins × OracleCoins) :=
  let SHA := Lift outside coin.2.2.1
  let earlier := before.run SHA
  StrandCanonicalExperiments.simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2.2 coin.2.1 coin.1

local notation "AuxiliaryCoins" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "PublicView" => Protocol.Execution.PublicView Context (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) Observed

def rawSimulate (coin : PublicCoins × AuxiliaryCoins) (SHA : Strand.Oracle) : PublicView :=
  let earlier := before.run SHA
  StrandCanonicalExperiments.simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata roundSampler batchingSamples SHA (requestOf earlier.1)
    (StrandGhostMerkle.Tree.labels Codec SHA coin.2.2 1) earlier.1 earlier.2
    (after earlier.1) coin.2.2 coin.2.1 coin.1


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalExperiments
