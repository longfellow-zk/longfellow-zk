import LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalRows
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalView

/-! Honest and public constructions of the complete guarded ghost view. These definitions contain no hiding proof. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms
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
local notation "BackendCoins" => CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)

local notation "Public" => configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
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
    (configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))
variable (SHA : Strand.Oracle)
local notation "H" => actualOracle binary prime primePlan binaryNodes scalars inputFits privateFits setup roundSampler SHA
local notation "honestFront" => FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars
  inputFits privateFits setup metadata original remaining H
local notation "publicFront" => FrontendCanonicalRows.publicBody binary prime primePlan binaryNodes scalars
  inputFits privateFits setup metadata H

variable {Context Observed : Type} {postQueries : ℕ}

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
  let cells := FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits original remaining coins.1 request
  let response := StrandCanonicalBackend.respondHonest (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount pCount metadata roundSampler batchingSamples request front SHA cells coins.2
  StrandCanonicalBackend.fullView (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
    bCount metadata roundSampler request context prior after leaves nonces front response SHA


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms (simulatedView honestView)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
