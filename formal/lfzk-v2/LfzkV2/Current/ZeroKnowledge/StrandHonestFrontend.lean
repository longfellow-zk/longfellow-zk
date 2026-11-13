import LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalRows

/-! Ordinary witness satisfaction makes the actual numbered-strand honest
frontend parse to satisfied backend equations. This is the body used definitionally
by `StrandCanonicalExecution.frontend`, without importing its statistical lemmas.
The oracle and committed root
are the ones supplied to the actual frontend constructor. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B) (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64)
variable (privateFits : binary.nPrivate < 2^64) (setup : FingerprintPrefix.Setup)
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Answer" => MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable {blocks : ℕ}
variable (roundSampler : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) setup binary.nPublic →
  Merkle.RandomOracle.Tree Strand.Word Strand.Digest
    (Option (MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)) blocks)

omit [DecidableEq B] in
/-- The actual honest frontend commits exactly the root supplied by its
indexed Merkle construction. This uses no witness or sampler premise. -/
theorem frontend_commitment
    (coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
    (request : Request) (root : Digest) (SHA : Strand.Oracle) :
    (FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original remaining
      (StrandCanonicalContext.actualOracle binary prime primePlan binaryNodes scalars
        inputFits privateFits setup roundSampler SHA) coins request root).commitment = root := rfl

/-- Parse and truth for the literal honest frontend, from ordinary witness
truth; hash truth is independent of R, the pads and the virtual leaves by the
circuit types. No parse or backend-truth
certificate is assumed. All reserved-mask quantification is derived inside. -/
theorem exists_satisfied
    (coins : CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
    (request : Request) (root : Digest) (SHA : Strand.Oracle)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : MdocWitness.HashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh request) (original request))
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))) :
    ∃ data,
      CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
        Repr Sh setup
        (StrandCanonicalContext.configuration binary prime primePlan binaryNodes scalars
          inputFits privateFits setup)
        (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits)
        pCount metadata request
        (FrontendCanonicalRows.honestBody binary prime primePlan binaryNodes scalars inputFits privateFits setup
          metadata original remaining
          (StrandCanonicalContext.actualOracle binary prime primePlan binaryNodes scalars
            inputFits privateFits setup roundSampler SHA) coins request root)
        (StrandCanonicalContext.actualOracle binary prime primePlan binaryNodes scalars
          inputFits privateFits setup roundSampler SHA) = some data ∧
      data.2.statement.1.Satisfies
        (Backend.logical (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
          original remaining coins request).1) ∧
      data.2.statement.2.Satisfies
        (Backend.logical (FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
          original remaining coins request).2) := by
  have uniform := MdocWitness.uniformHashValid_of_valid valid
  exact FrontendCanonicalRows.exists_satisfied binary prime primePlan binaryNodes scalars inputFits privateFits
    setup metadata original remaining
    (StrandCanonicalContext.actualOracle binary prime primePlan binaryNodes scalars
      inputFits privateFits setup roundSampler SHA)
    coins request root pivotOne primitive
    (FrontendCanonicalRows.couplingHash_of_valid binary prime primePlan binaryNodes scalars
      inputFits privateFits setup metadata original _ request root uniform)
    (FrontendCanonicalRows.hashTruth_of_valid binary prime primePlan binaryNodes scalars
      inputFits privateFits setup metadata original remaining _ request root coins uniform)
    signature

end LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
