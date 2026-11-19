import LfzkV2.Current.CanonicalRequest
import LfzkV2.Current.Mdoc.Runtime
import LfzkV2.Current.Protocol.ExecutionSampler
import LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
import LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
import LfzkV2.Current.ZeroKnowledge.StrandHonestCompletion
import LfzkV2.Current.ZeroKnowledge.StrandHonestSampled

/-! Completeness of the current indexed honest runtime, from ordinary
witness truth and the static circuit premise.

`prove` is the honest prover at one request and witness: it returns a proof
unless the challenge reader aborts. `some_accepts` shows that every proof it
returns is accepted. `prove_some` shows that it returns a proof whenever the
reader returns a value at every ordinary boundary, so that `accepts`, the
two together, is deterministic and has no abort branch left. The actual
experiment, with its observers, runs this same prover (`rawReal_output`).
`Mdoc.Completeness.accepts_rust` bounds the reader's aborts for the Rust
reader. -/
noncomputable section
namespace LfzkV2.Current.Mdoc.Completeness
open LfzkV2.Current.ZeroKnowledge
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (runtime : Mdoc.Runtime B)
local notation "Sh" => MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
  (RuntimeStatement.degreeFits runtime.binary)
local notation "Answer" => MdocRuntime.Answer runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.binaryNodes
local notation "Request" => CanonicalRequest.Request Sh runtime.binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) runtime.binary.description Sh
local notation "pCount" => RuntimeStatement.prime_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits
local notation "Fmt" => MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint
variable {blocks : ℕ}
variable (sampler : Protocol.ExecutionSampler runtime.protocol blocks)
local notation "roundSampler" => sampler.sample

local notation "Public" => StrandCanonicalContext.configuration runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars
  runtime.inputFits runtime.privateFits runtime.fingerprint
local notation "BackendCoins" => Backend.JointMasks runtime.binaryNodes ConcreteSetup.primeNodes runtime.binary.description.cells
  (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads)
local notation "HonestCoins" => (CompleteHonest.Tape runtime.binary runtime.prime × CompleteHonest.Masks (B := B)) × BackendCoins
local notation "Codec" => StrandCanonicalBackend.indexedCodec runtime.binary.description runtime.prime runtime.binaryNodes
  ConcreteSetup.primeNodes (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public
local notation "ToLeaf" => StrandCanonicalBackend.leafEquiv runtime.binary.description runtime.prime runtime.binaryNodes
  ConcreteSetup.primeNodes (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public
variable (batchingSamples : MdocRuntime.Answer runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.binaryNodes →
  RuntimeVerifier.RawSamples runtime.binary.description runtime.prime
    (backend runtime.binaryNodes runtime.binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads))
    (CompleteCanonicalVerifier.publicConfig runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
      (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
      (StrandCanonicalContext.configuration runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint)))

/-- The actual runtime verifier of the setup. -/
def verify (SHA : Strand.Oracle) (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) runtime.binary.description
    (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits
      runtime.privateFits (RuntimeStatement.degreeFits runtime.binary))) : Bool :=
    StrandVerifier.verify runtime.binary.description runtime.prime
      (backend runtime.binaryNodes runtime.binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads))
      (CompleteCanonicalVerifier.publicConfig runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
        (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public)
      (CompleteCanonicalVerifier.earlier runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
        Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) runtime.metadata)
      (Format.wire (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)) (Format.body (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)) roundSampler
      (Format.hashPublic (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint))
      (CanonicalRuntime.decodePrimePublic runtime.binary.description runtime.prime
        (backend runtime.binaryNodes runtime.binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads)) (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
        (CompleteCanonicalVerifier.basePublic runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
          (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public) pCount)
      batchingSamples Codec SHA id output

/-- The reader returns a value at every ordinary boundary of `SHA`. -/
def Sampled (SHA : Strand.Oracle) : Prop :=
  ∀ (index : Fin (MdocRuntime.geometry runtime.binary.description runtime.prime runtime.binary.plan
      runtime.primePlan).roles.length) history block,
    TranscriptV2.StrandVerifier.sampled (StrandRuntime.history (Fmt).wire (Fmt).body) roundSampler SHA
      ((.round index history block : (Fmt).Point))

section Prover
variable (original : Fin runtime.binary.nPrivate → Bool)
variable (remaining : Fin runtime.prime.remaining → Adapter.Mdoc.P)
variable (request : CanonicalRequest.Request
  (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
    (RuntimeStatement.degreeFits runtime.binary)) runtime.binary.nPublic)

/-- The honest prover at one request and witness: the proof component of
the honest experiment (`StrandCanonicalExecution.rawReal`) with no observer
queries. It commits to the columns, runs the frontend and the backend, and
completes the proof; it returns `none` exactly when the backend returns no
response or no opening (`StrandHonestExecution.rawReal_result`). Its ghost
labels are unused. -/
def prove (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce) (SHA : Strand.Oracle) :
    Option Output :=
  (StrandCanonicalExecution.rawReal runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes runtime.scalars
    runtime.inputFits runtime.privateFits runtime.fingerprint runtime.metadata (fun _ : Unit => original)
    (fun _ => remaining) roundSampler batchingSamples (.done () : Merkle.RandomOracle.Tree Bytes Digest Unit 0)
    (fun _ => request) (fun _ _ => (.done () : Merkle.RandomOracle.Tree Bytes Digest Unit 0))
    (coins,(nonces,fun _ => 0)) SHA).2.1.1

end Prover

section Experiment
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (original : Context → Fin runtime.binary.nPrivate → Bool)
variable (remaining : Context → Fin runtime.prime.remaining → Adapter.Mdoc.P)
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

/-- The actual experiment's proof is the honest prover's output at the
context its prior observer returns. Its ghost labels are unused. -/
theorem rawReal_output (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle) :
    (Raw (coins,(nonces,ghost)) SHA).2.1.1 =
      prove runtime sampler batchingSamples (original (before.run SHA).1) (remaining (before.run SHA).1)
        (requestOf (before.run SHA).1) coins nonces SHA := by
  unfold prove
  rw [StrandHonestExecution.rawReal_result, StrandHonestExecution.rawReal_result]
  rfl

/-- Honest acceptance for a proof returned by the actual numbered-strand
experiment. Parser, backend response, physical selector, indexed
authentication and final-seal facts are all derived from execution. -/
private theorem experiment_accepts (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle)
    (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) runtime.binary.description Sh)
    (produced : (Raw (coins,(nonces,ghost)) SHA).2.1.1 = some output)
    (pivotOne : runtime.binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX runtime.binary.basis) = true)
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
        (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public)
      (CompleteCanonicalVerifier.earlier runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
        Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) runtime.metadata)
      (Format.wire (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)) (Format.body (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)) roundSampler
      (Format.hashPublic (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint))
      (CanonicalRuntime.decodePrimePublic runtime.binary.description runtime.prime
        (backend runtime.binaryNodes runtime.binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells runtime.prime.remaining runtime.prime.pads)) (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
        (CompleteCanonicalVerifier.basePublic runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes
          (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public) pCount)
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
    pivotOne primitive valid signature
  have truth : ∀ next,
      CompleteCanonicalVerifier.statementAt runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint)
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
    (MdocRuntime.format runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.scalars runtime.inputFits runtime.privateFits (RuntimeStatement.degreeFits runtime.binary) runtime.fingerprint) Public (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) runtime.metadata roundSampler
    pCount batchingSamples request front SHA cells coins.2 responses indices opened nonces truth generated committed
  rw [finished]
  simpa only [context,request,root,front,cells,StrandCanonicalExecution.columns,
    Equiv.symm_apply_apply] using accepted


end Experiment

section Endpoints
variable (original : Fin runtime.binary.nPrivate → Bool)
variable (remaining : Fin runtime.prime.remaining → Adapter.Mdoc.P)
variable (request : CanonicalRequest.Request
  (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits runtime.privateFits
    (RuntimeStatement.degreeFits runtime.binary)) runtime.binary.nPublic)
variable (pivotOne : runtime.binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX runtime.binary.basis) = true)
variable (valid : MdocWitness.HashValid
  (RequestedSimulator.requestedBinary runtime.binary runtime.prime runtime.primePlan
    (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits
      runtime.privateFits (RuntimeStatement.degreeFits runtime.binary)) request) original)
variable (signature :
  let b := RequestedSimulator.requestedBinary runtime.binary runtime.prime runtime.primePlan
    (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits
      runtime.privateFits (RuntimeStatement.degreeFits runtime.binary)) request
  let p := RequestedSimulator.requestedPrime runtime.binary runtime.prime runtime.primePlan
    (MdocRuntime.shape runtime.binary.description runtime.prime runtime.binary.plan runtime.primePlan runtime.inputFits
      runtime.privateFits (RuntimeStatement.degreeFits runtime.binary))
    (RuntimeStatement.prime_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits) request
  p.circuit.Satisfies (CompleteHonest.primeInputs b p original remaining))

include pivotOne primitive valid signature in
/-- Every proof the honest prover returns is accepted by the runtime
verifier. -/
theorem some_accepts (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce) (SHA : Strand.Oracle)
    (output : Output)
    (produced : prove runtime sampler batchingSamples original remaining request coins nonces SHA = some output) :
    verify runtime sampler batchingSamples SHA output = true := by
  exact experiment_accepts runtime sampler batchingSamples (fun _ : Unit => original) (fun _ => remaining)
    (.done ()) (fun _ => request) (fun _ _ => (.done () : Merkle.RandomOracle.Tree Bytes Digest Unit 0))
    coins nonces (fun _ => 0) SHA output produced pivotOne primitive valid signature

include pivotOne primitive valid signature in
/-- Deterministic non-abort: when the reader returns a value at every
ordinary boundary, the honest prover returns a proof. -/
theorem prove_some (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce) (SHA : Strand.Oracle)
    (sampled : Sampled runtime sampler SHA) :
    ∃ output, prove runtime sampler batchingSamples original remaining request coins nonces SHA = some output := by
  let root := StrandHonestExecution.committedRoot runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes
    runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint
    (fun _ : Unit => original) (fun _ => remaining) (fun _ => request) coins nonces () SHA
  obtain ⟨data,parsed,_⟩ := StrandHonestFrontend.exists_satisfied runtime.binary runtime.prime runtime.primePlan
    runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint runtime.metadata
    (fun _ => original) (fun _ => remaining) roundSampler coins.1 request root SHA pivotOne primitive valid signature
  obtain ⟨responses,indices,opened,generated⟩ := StrandCanonicalBackend.respondHonest_selected
    runtime.binary.description runtime.prime runtime.binaryNodes ConcreteSetup.primeNodes (Fmt) Public
    (RuntimeStatement.binary_count runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits)
    pCount runtime.metadata roundSampler batchingSamples request
    (StrandCanonicalExecution.frontend runtime.binary runtime.prime runtime.primePlan runtime.binaryNodes
      runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint runtime.metadata
      (fun _ : Unit => original) (fun _ => remaining) roundSampler coins.1 () request root SHA) SHA
    (FrontendCanonicalRows.cells runtime.binary runtime.prime runtime.primePlan runtime.inputFits runtime.privateFits
      (fun _ => original) (fun _ => remaining) coins.1 request) coins.2
    (by rw [Option.isSome_iff_exists]; exact ⟨data, parsed⟩)
    (StrandCanonicalBackend.sampled_round runtime.binary.description (Fmt) roundSampler SHA sampled)
  have response : StrandCanonicalExecution.response runtime.binary runtime.prime runtime.primePlan
      runtime.binaryNodes runtime.scalars runtime.inputFits runtime.privateFits runtime.fingerprint runtime.metadata
      (fun _ : Unit => original) (fun _ => remaining) roundSampler batchingSamples coins () request root SHA =
      some (responses,some ⟨indices,opened⟩) := generated
  unfold prove
  rw [StrandHonestExecution.rawReal_result]
  simp only [Merkle.RandomOracle.Tree.run_done]
  rw [response]
  exact ⟨_, rfl⟩

include pivotOne primitive valid signature in
/-- Completeness: when the reader returns a value at every ordinary boundary,
the honest prover returns a proof and the runtime verifier accepts it. -/
theorem accepts (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce) (SHA : Strand.Oracle)
    (sampled : Sampled runtime sampler SHA) :
    ∃ output, prove runtime sampler batchingSamples original remaining request coins nonces SHA = some output ∧
      verify runtime sampler batchingSamples SHA output = true := by
  obtain ⟨output, produced⟩ := prove_some runtime sampler batchingSamples original remaining request
    pivotOne primitive valid signature coins nonces SHA sampled
  exact ⟨output, produced, some_accepts runtime sampler batchingSamples original remaining request
    pivotOne primitive valid signature coins nonces SHA output produced⟩

end Endpoints
end LfzkV2.Current.Mdoc.Completeness
