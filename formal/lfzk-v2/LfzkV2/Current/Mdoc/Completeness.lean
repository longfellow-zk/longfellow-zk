import LfzkV2.Current.Mdoc.Runtime
import LfzkV2.Current.Protocol.ExecutionSampler
import LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
import LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
import LfzkV2.Current.ZeroKnowledge.StrandHonestCompletion

/-! Every actual proof returned by the current indexed honest runtime is
accepted, from ordinary witness truth and the static circuit premise. -/
noncomputable section
namespace LfzkV2.Current.Mdoc.Completeness
open LfzkV2.Current.ZeroKnowledge
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (runtime : Mdoc.Runtime B)
local notation "Sh" => MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
  (RuntimeStatement.degreeFits runtime.binary)
local notation "Repr" => MdocRuntime.representations runtime.scalars
local notation "Answer" => MdocRuntime.Answer runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.binaryNodes
local notation "Request" => CanonicalRequest.Request Sh runtime.binary.nPublic
local notation "pCount" => RuntimeStatement.prime_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (original : Context → Fin runtime.binary.nPrivate → Bool)
variable (remaining : Context → Fin runtime.prime.remaining → Adapter.Mdoc.P)
variable {blocks : ℕ}
variable (sampler : Protocol.ExecutionSampler runtime.protocol blocks)
local notation "roundSampler" => sampler.sample

local notation "Public" => StrandCanonicalContext.configuration runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars
  runtime.inputFits runtime.privateFits runtime.fingerprint
local notation "BackendCoins" => Backend.JointMasks runtime.binaryNodes ConcreteSetup.primeNodes runtime.binary.description.cells
  (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads)
local notation "HonestCoins" => (CompleteHonest.Tape runtime.binary runtime.prime × CompleteHonest.Masks (B := B)) × BackendCoins
local notation "Codec" => StrandCanonicalBackend.indexedCodec runtime.binary.description runtime.prime runtime.binaryNodes
  ConcreteSetup.primeNodes Repr Sh runtime.fingerprint Public
local notation "ToLeaf" => StrandCanonicalBackend.leafEquiv runtime.binary.description runtime.prime runtime.binaryNodes
  ConcreteSetup.primeNodes Repr Sh runtime.fingerprint Public
variable (batchingSamples : MdocRuntime.Answer runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.binaryNodes →
  RuntimeVerifier.RawSamples runtime.binary.description runtime.prime
    (backend runtime.binaryNodes runtime.binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads))
    (CompleteCanonicalVerifier.publicConfig runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
      (MdocRuntime.representations runtime.scalars)
      (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
        (RuntimeStatement.degreeFits runtime.binary)) runtime.fingerprint
      (StrandCanonicalContext.configuration runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint)))
variable (before : Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
    (RuntimeStatement.degreeFits runtime.binary)) runtime.binary.nPublic)
variable (after : Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) runtime.binary.description
  (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
    (RuntimeStatement.degreeFits runtime.binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
local notation "Columns" => StrandCanonicalExecution.columns runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
  original remaining requestOf
local notation "Front" => StrandCanonicalExecution.frontend runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
  runtime.metadata original remaining roundSampler
local notation "Response" => StrandCanonicalExecution.response runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
  runtime.metadata original remaining roundSampler batchingSamples
local notation "Raw" => StrandCanonicalExecution.rawReal runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
  runtime.metadata original remaining roundSampler batchingSamples before requestOf after

/-- End-to-end honest acceptance for a proof returned by the actual
numbered-strand experiment. Parser, backend response, physical selector,
indexed authentication and final-seal facts are all derived from execution. -/
theorem rawReal_some_accepts (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle)
    (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) runtime.binary.description Sh)
    (produced : (Raw (coins,(nonces,ghost)) SHA).2.1.1 = some output)
    (pivotOne : runtime.binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX runtime.binary.basis) = true)
    (separated : MdocWitness.ReadDisjoint runtime.binary)
    (valid : MdocWitness.HashValid
      (RequestedSimulator.requestedBinary runtime.binary runtime.prime runtime.primePlan Sh (requestOf (before.run SHA).1))
      (original ((before.run SHA).1)))
    (signature :
      let request := requestOf (before.run SHA).1
      let b := RequestedSimulator.requestedBinary runtime.binary runtime.prime runtime.primePlan Sh request
      let p := RequestedSimulator.requestedPrime runtime.binary runtime.prime runtime.primePlan Sh pCount request
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original (before.run SHA).1) (remaining (before.run SHA).1))) :
    StrandVerifier.verify runtime.binary.description runtime.prime
      (backend runtime.binaryNodes runtime.binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads))
      (CompleteCanonicalVerifier.publicConfig runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
        Repr Sh runtime.fingerprint Public)
      (CompleteCanonicalVerifier.earlier runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes Repr Sh runtime.fingerprint
        Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) runtime.metadata)
      (ProofBodyCodec.codec Repr (MdocRuntime.geometry runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan)) roundSampler
      (CanonicalRequest.hashPublic runtime.binary.description.nPublic)
      (CanonicalRuntime.decodePrimePublic runtime.binary.description runtime.prime
        (backend runtime.binaryNodes runtime.binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads)) Repr Sh runtime.fingerprint
        (CompleteCanonicalVerifier.basePublic runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
          Repr Sh runtime.fingerprint Public) pCount)
      batchingSamples Codec SHA id output = true := by
  let context := (before.run SHA).1
  let request := requestOf context
  let root := StrandHonestExecution.committedRoot runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
    original remaining requestOf coins nonces context SHA
  let front := Front coins.1 context request root SHA
  let cells := FrontendCanonicalRows.cells runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits
    (fun _ => original context) (fun _ => remaining context) coins.1 request
  obtain ⟨responses,indices,opened,generated,finished⟩ :=
    StrandHonestExecution.rawReal_some runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
      runtime.metadata original remaining roundSampler batchingSamples before requestOf after coins nonces ghost SHA output produced
  obtain ⟨data,parsed,holds⟩ := StrandHonestFrontend.exists_satisfied runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars
    runtime.inputFits runtime.privateFits runtime.fingerprint runtime.metadata (fun _ => original context) (fun _ => remaining context) roundSampler coins.1 request root SHA
    pivotOne primitive (MdocWitness.noninterference_of_readDisjoint runtime.binary separated) valid signature
  have truth : ∀ next,
      CompleteCanonicalVerifier.statementAt runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes Repr Sh runtime.fingerprint
        Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) pCount runtime.metadata request front
        (StrandCanonicalContext.actualOracle runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars
          runtime.inputFits runtime.privateFits runtime.fingerprint roundSampler SHA) = some next →
      next.2.statement.1.Satisfies (Backend.logical cells.1) ∧
        next.2.statement.2.Satisfies (Backend.logical cells.2) := by
    intro next nextParsed
    have same := Option.some.inj (parsed.symm.trans nextParsed)
    cases same
    exact holds
  have committed : front.commitment = Merkle.Indexed.root ((Codec).withOracle SHA) 2443
      (fun index => (index,nonces index))
      (fun index => ToLeaf (StrandCanonicalBackend.committedColumns runtime.binary.description runtime.prime runtime.binaryNodes
        ConcreteSetup.primeNodes cells coins.2 index)) := by
    exact StrandHonestFrontend.frontend_commitment runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits
      runtime.fingerprint runtime.metadata (fun _ => original context) (fun _ => remaining context) roundSampler coins.1 request root SHA
  have accepted := StrandCanonicalBackend.respondHonest_accepts runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
    Repr Sh runtime.fingerprint Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) runtime.metadata roundSampler
    pCount batchingSamples request front SHA cells coins.2 responses indices opened nonces truth generated committed
  rw [finished]
  simpa only [context,request,root,front,cells,StrandCanonicalExecution.columns,
    Equiv.symm_apply_apply] using accepted

end LfzkV2.Current.Mdoc.Completeness
