import LfzkV2.Current.ZeroKnowledge.StrandCanonicalExecution

/-! The successful result of the actual indexed honest experiment is the
canonical completion of its committed columns and original nonce tape. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
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
variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (original : Context → Fin binary.nPrivate → Bool)
variable (remaining : Context → Fin prime.remaining → Adapter.Mdoc.P)
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

/-- The honest root is computed from all original physical columns and
nonces before any frontend or backend challenge is sampled. -/
def committedRoot (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (context : Context) (SHA : Strand.Oracle) : Digest :=
  Merkle.Indexed.commitLabels ((Codec).withOracle SHA) 2443
    (fun index => (index,nonces index)) (Columns coins context) 1

/-- The actual experiment's proof component, including every abort branch.
The arbitrary ghost labels in its auxiliary coin tape are unused. -/
theorem rawReal_result (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle) :
    let context := (before.run SHA).1
    let request := requestOf context
    let root := committedRoot binary prime primePlan binaryNodes scalars inputFits privateFits setup
      original remaining requestOf coins nonces context SHA
    (Raw (coins,(nonces,ghost)) SHA).2.1.1 =
      match Response coins context request root SHA with
      | none | some (_,none) => none
      | some (responses,some ⟨indices,_⟩) =>
        some (StrandCanonicalBackend.finish binary.description prime binaryNodes ConcreteSetup.primeNodes
          Repr Sh setup Public (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits)
          metadata roundSampler request (Front coins.1 context request root SHA) responses indices
          (fun index => (ToLeaf).symm (Columns coins context index.val))
          (Merkle.Indexed.openCore ((Codec).withOracle SHA) 2443 (OrderedOpening.query indices).coordinates
            (fun index => (index,nonces index)) (Columns coins context)) SHA) := by
  unfold StrandCanonicalHiding.rawReal StrandGhostMerkle.Schedule.honest
  dsimp only
  unfold committedRoot
  rw [StrandCanonicalHiding.stage_eq binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples requestOf after coins (before.run SHA).1 SHA
    _]
  cases backend : Response coins (before.run SHA).1 (requestOf (before.run SHA).1)
      (Merkle.Indexed.commitLabels ((Codec).withOracle SHA) 2443
        (fun index => (index,nonces index)) (Columns coins (before.run SHA).1) 1) SHA with
  | none => simp only [StrandCanonicalBackend.prepare,Merkle.RandomOracle.Tree.run_map]
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => simp only [StrandCanonicalBackend.prepare,Merkle.RandomOracle.Tree.run_map]
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          simp only [StrandCanonicalBackend.prepare,Merkle.RandomOracle.Tree.run_map]

/-- Every proof actually returned by the honest experiment is completed
from the original committed columns and nonces, with an actual successful
backend response. This derives the constructor equation from execution. -/
theorem rawReal_some (coins : HonestCoins) (nonces : Fin 2443 → MerkleNonce)
    (ghost : Fin 2443 → Digest) (SHA : Strand.Oracle)
    (output : CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh)
    (produced : (Raw (coins,(nonces,ghost)) SHA).2.1.1 = some output) :
    let context := (before.run SHA).1
    let request := requestOf context
    let root := committedRoot binary prime primePlan binaryNodes scalars inputFits privateFits setup
      original remaining requestOf coins nonces context SHA
    ∃ responses indices opened,
      Response coins context request root SHA = some (responses,some ⟨indices,opened⟩) ∧
      output = StrandCanonicalBackend.finish binary.description prime binaryNodes ConcreteSetup.primeNodes
        Repr Sh setup Public (RuntimeStatement.binary_count binary prime primePlan inputFits privateFits)
        metadata roundSampler request (Front coins.1 context request root SHA) responses indices
        (fun index => (ToLeaf).symm (Columns coins context index.val))
        (Merkle.Indexed.openCore ((Codec).withOracle SHA) 2443 (OrderedOpening.query indices).coordinates
          (fun index => (index,nonces index)) (Columns coins context)) SHA := by
  dsimp only
  rw [rawReal_result binary prime primePlan binaryNodes scalars inputFits privateFits setup
    metadata original remaining roundSampler batchingSamples before requestOf after coins nonces ghost SHA] at produced
  cases backend : Response coins (before.run SHA).1 (requestOf (before.run SHA).1)
      (committedRoot binary prime primePlan binaryNodes scalars inputFits privateFits setup
        original remaining requestOf coins nonces (before.run SHA).1 SHA) SHA with
  | none => simp only [backend,reduceCtorEq] at produced
  | some result =>
      rcases result with ⟨responses,selection⟩
      cases selection with
      | none => simp only [backend,reduceCtorEq] at produced
      | some selected =>
          rcases selected with ⟨indices,opened⟩
          refine ⟨responses,indices,opened,rfl,?_⟩
          simpa only [backend,Option.some.injEq] using produced.symm

end LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
