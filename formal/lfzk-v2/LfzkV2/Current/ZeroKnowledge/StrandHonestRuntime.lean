import LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
import LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
import LfzkV2.Current.ZeroKnowledge.StrandHonestCompletion

/-! Every actual proof returned by the current indexed honest runtime is
accepted, from ordinary witness truth and the static circuit premise. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandHonestRuntime
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

local notation "Public" => StrandCanonicalFullCoupling.configuration binary prime primePlan binaryNodes scalars
  inputFits privateFits setup
local notation "BackendCoins" => CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "HonestCoins" => (CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) × BackendCoins
local notation "Codec" => StrandCanonicalBackend.indexedCodec binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
local notation "ToLeaf" => StrandCanonicalBackend.leafEquiv binary.description prime binaryNodes
  ConcreteSetup.primeNodes Repr Sh setup Public
variable (batchingSamples : MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes →
  RuntimeVerifier.RawSamples binary.description prime
    (backend binaryNodes binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes
      (MdocRuntime.representations scalars)
      (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
        (RuntimeStatement.degreeFits binary)) setup
      (StrandCanonicalFullCoupling.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup)))
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
local notation "Columns" => StrandCanonicalHiding.columns binary prime primePlan binaryNodes scalars inputFits privateFits setup
  original remaining requestOf
local notation "Front" => StrandCanonicalHiding.frontend binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler
local notation "Response" => StrandCanonicalHiding.response binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples
local notation "Raw" => StrandCanonicalHiding.rawReal binary prime primePlan binaryNodes scalars inputFits privateFits setup
  metadata original remaining roundSampler batchingSamples before requestOf after

/-- End-to-end honest acceptance for a proof returned by the actual
numbered-strand experiment. Parser, backend response, physical selector,
indexed authentication and final-seal facts are all derived from execution. -/
theorem rawReal_some_accepts (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle)
    (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh)
    (produced : (Raw (coins,(nonces,ghost)) SHA).2.1.1 = some output)
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (independent : MdocWitness.HashNoninterference binary)
    (valid : MdocWitness.HashValid
      (RequestedSimulator.requestedBinary binary prime primePlan Sh (requestOf (before.run SHA).1))
      (original (requestOf (before.run SHA).1)))
    (signature :
      let request := requestOf (before.run SHA).1
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))) :
    StrandVerifier.verify binary.description prime
      (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
      (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes
        Repr Sh setup Public)
      (CompleteCanonicalVerifier.earlier binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup
        Public (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits) metadata)
      (ProofBodyCodec.codec Repr (MdocRuntime.geometry binary.description prime binary.plan primePlan)) roundSampler
      (CanonicalRequest.hashPublic binary.description.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime
        (backend binaryNodes binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) Repr Sh setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes
          Repr Sh setup Public) pCount)
      batchingSamples Codec SHA id output = true := by
  let context := (before.run SHA).1
  let request := requestOf context
  let root := StrandHonestExecution.committedRoot binary prime primePlan binaryNodes scalars inputFits privateFits setup
    original remaining requestOf coins nonces context SHA
  let front := Front coins.1 request root SHA
  let cells := FrontendCanonicalRows.cells binary prime primePlan inputFits privateFits
    original remaining coins.1 request
  obtain ⟨responses,indices,opened,generated,finished⟩ :=
    StrandHonestExecution.rawReal_some binary prime primePlan binaryNodes scalars inputFits privateFits setup
      metadata original remaining roundSampler batchingSamples before requestOf after coins nonces ghost SHA output produced
  obtain ⟨data,parsed,holds⟩ := StrandHonestFrontend.exists_satisfied binary prime primePlan binaryNodes scalars
    inputFits privateFits setup metadata original remaining roundSampler coins.1 request root SHA
    pivotOne primitive independent valid signature
  have truth : ∀ next,
      CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup
        Public (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits) pCount metadata request front
        (StrandCanonicalFullCoupling.actualOracle binary prime primePlan binaryNodes scalars
          inputFits privateFits setup roundSampler SHA) = some next →
      next.2.statement.1.Satisfies (Backend.logical cells.1) ∧
        next.2.statement.2.Satisfies (Backend.logical cells.2) := by
    intro next nextParsed
    have same := Option.some.inj (parsed.symm.trans nextParsed)
    cases same
    exact holds
  have committed : front.commitment = Merkle.Indexed.root ((Codec).withOracle SHA) 2443
      (fun index => (index,nonces index))
      (fun index => ToLeaf (StrandCanonicalBackend.committedColumns binary.description prime binaryNodes
        ConcreteSetup.primeNodes cells coins.2 index)) := by
    exact StrandHonestFrontend.frontend_commitment binary prime primePlan binaryNodes scalars inputFits privateFits
      setup metadata original remaining roundSampler coins.1 request root SHA
  have accepted := StrandCanonicalBackend.respondHonest_accepts binary.description prime binaryNodes ConcreteSetup.primeNodes
    Repr Sh setup Public (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits) metadata roundSampler
    pCount batchingSamples request front SHA cells coins.2 responses indices opened nonces truth generated committed
  rw [finished]
  simpa only [context,request,root,front,cells,StrandCanonicalHiding.columns,
    Equiv.symm_apply_apply] using accepted

end LfzkV2.Current.ZeroKnowledge.StrandHonestRuntime
