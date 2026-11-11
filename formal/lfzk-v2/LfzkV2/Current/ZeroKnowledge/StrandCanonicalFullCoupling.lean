import LfzkV2.Current.ZeroKnowledge.StrandCanonicalPrograms

/-! Exact joint frontend/backend coin equivalence at a fixed oracle and ghost commitment. No statistical commitment argument enters this module. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
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

theorem statementTruth (coins : FrontendCoins) (request : Request) (root : Digest)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : MdocWitness.UniformHashValid (RequestedSimulator.requestedBinary binary prime primePlan Sh request) (original request))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))) :
    ∀ data, CompleteCanonicalVerifier.statementAt (g := G) (fields := MdocRuntime.fields B)
      (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Public bCount pCount metadata request (honestFront coins request root) H = some data →
      data.2.statement.1.Satisfies
        (Backend.logical (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits original remaining coins request).1) ∧
      data.2.statement.2.Satisfies
        (Backend.logical (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits original remaining coins request).2) := by
  intro data parsed
  obtain ⟨known,parsedKnown,truth⟩ := FrontendCanonicalRows.exists_satisfied binary prime primePlan binaryNodes scalars
    inputFits privateFits setup metadata original remaining H coins request root pivotOne primitive
    (FrontendCanonicalRows.couplingHash_of_valid binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original H request root valid)
    (FrontendCanonicalRows.hashTruth_of_valid binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original remaining H request root coins valid) signature
  have same : known = data := Option.some.inj (parsedKnown.symm.trans parsed)
  subst data
  exact truth

variable {Context Observed : Type} {postQueries : ℕ}

/-- Change backend masks at the fixed honest frontend, then change the
frontend coins. The inverse first recovers the honest frontend coins, which
identify the backend fiber to invert. This preserves uniform joint coins
although the backend statement depends on the frontend messages. -/
def coupling (request : Request) (root : Digest) (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : MdocWitness.UniformHashValid (RequestedSimulator.requestedBinary binary prime primePlan Sh request) (original request))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))) :
    (FrontendCoins × BackendCoins) ≃ (CompleteSimulation.Coins binary prime × BackendCoins) :=
  let frontEquiv := FrontendCanonicalRows.frontendCoupling binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining H request root pivotOne
    (FrontendCanonicalRows.couplingHash_of_valid binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original H request root valid)
  let backendEquiv := fun coins : FrontendCoins =>
    StrandCanonicalBackend.responseCoupling (g := G) (fields := MdocRuntime.fields B)
      (Advice := MdocAdvice.Value) (C := Answer) binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Public
      bCount pCount metadata roundSampler batchingSamples request (honestFront coins request root) SHA
      (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits original remaining coins request)
      (statementTruth binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining roundSampler SHA
        coins request root pivotOne primitive valid signature)
  (Equiv.prodCongrRight backendEquiv).trans (frontEquiv.prodCongr (Equiv.refl BackendCoins))

theorem complete_view (request : Request) (root : Digest) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : MdocWitness.UniformHashValid (RequestedSimulator.requestedBinary binary prime primePlan Sh request) (original request))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request)))
    (coins : FrontendCoins × BackendCoins) :
    simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata roundSampler batchingSamples SHA
      request root context prior after leaves nonces
      (coupling binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining roundSampler
        batchingSamples SHA request root pivotOne primitive valid signature coins) =
    honestView binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining roundSampler
      batchingSamples SHA request root context prior after leaves nonces coins := by
  rcases coins with ⟨frontendCoins,backendCoins⟩
  have front := FrontendCanonicalRows.frontend_view binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata
    original remaining H request root pivotOne
    (FrontendCanonicalRows.couplingHash_of_valid binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original H request root valid) frontendCoins
  simp only [simulatedView,honestView,coupling,Equiv.trans_apply,Equiv.prodCongr_apply,Equiv.prodCongrRight_apply,
    Equiv.refl_apply,Prod.map]
  rw [← front]
  rw [StrandCanonicalBackend.backend_view]

/-- Uniform backend masks have a finite representation independently of
how the complete application configuration is reduced. -/
local instance backendCoinsFintype : Fintype BackendCoins := Fintype.ofFinite _

/-- At a fixed oracle and ghost commitment, changing only prover coins
removes the witness from the complete public view. The view retains the
prior context and trace, canonical proof, and later observer result and trace.
The statistical commitment-hiding step is separate from this exact law. -/
theorem sameDistribution (request : Request) (root : Digest) (context : Context) (prior : List (Bytes × Digest))
    (after : Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh) →
      Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
    (leaves : Fin 2443 → Digest) (nonces : Fin 2443 → MerkleNonce)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : MdocWitness.UniformHashValid (RequestedSimulator.requestedBinary binary prime primePlan Sh request) (original request))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))) :
    LigeroFamily.SameDistribution
      (honestView binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
        roundSampler batchingSamples SHA request root context prior after leaves nonces)
      (simulatedView binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata
        roundSampler batchingSamples SHA request root context prior after leaves nonces) := by
  apply LigeroFamily.sameDistribution_of_equiv
    (coupling binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
      roundSampler batchingSamples SHA request root pivotOne primitive valid signature)
  intro coins
  exact (complete_view binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining
    roundSampler batchingSamples SHA request root context prior after leaves nonces
    pivotOne primitive valid signature coins).symm

end LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
