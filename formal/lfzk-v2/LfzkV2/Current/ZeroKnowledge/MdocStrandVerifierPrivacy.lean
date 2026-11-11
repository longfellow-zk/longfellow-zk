import LfzkV2.Current.ZeroKnowledge.MdocStrandZeroKnowledge
import LfzkV2.Current.ZeroKnowledge.StrandVerifierObserver

/-! Instantiate the complete privacy theorem with the actual runtime
verifier as the post-proof observer. This connects its accepted/rejected
bit, including simulator aborts, to the compared observable distributions. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocStrandVerifierPrivacy
open Application ApplicationSetup ConcreteSetup Frontend TranscriptV2 LigeroFamily Merkle.RandomOracle
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
attribute [local instance] StrandCanonicalHiding.honestCoinsFintype StrandCanonicalHiding.publicCoinsFintype
attribute [local irreducible] MdocRuntime.geometry
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "G" => MdocRuntime.geometry binary.description prime.description binary.plan prime.plan
local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Answer" => MdocRuntime.Answer binary.description prime.description binary.plan prime.plan Nodes
local notation "Setup" visible => MdocSetupFamily.setup binary prime cantor scalars ids bounds visible
local notation "Values" SHA => MdocSetupFamily.values binary prime cantor scalars ids bounds SHA
local notation "Private" => (CompleteHonest.Tape binary prime.description × CompleteHonest.Masks (B := B)) ×
  CompleteBackend.Masks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Public" => CompleteSimulation.Coins binary prime.description ×
  CompleteBackend.Masks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Auxiliary" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "HonestCoins" => Private × Auxiliary
local notation "SimulatorCoins" => Public × Auxiliary
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description Sh

variable {Context : Type} {preQueries blocks : ℕ}
variable (sample : (visible : MdocSetupFamily.Values) →
  QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
    (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
      bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))
    (MdocSetupFamily.setup binary prime cantor scalars ids bounds visible) binary.nPublic →
    Merkle.RandomOracle.Tree Strand.Word Digest
      (Option (MdocRuntime.Answer binary.description prime.description binary.plan prime.plan
        (ConcreteSetup.binaryNodes cantor))) blocks)
variable (before : MdocSetupFamily.Values → Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin prime.description.remaining → Adapter.Mdoc.P)

local notation "Cfg" visible => StrandCanonicalFullCoupling.configuration binary prime.description prime.plan Nodes scalars
  bounds.inputFits bounds.privateFits (Setup visible)
local notation "Wire" visible => CompleteCanonicalVerifier.publicConfig binary.description prime.description Nodes
  ConcreteSetup.primeNodes Repr Sh (Setup visible) (Cfg visible)
local notation "First" => ConcreteSetup.backend Nodes binary.description.cells
local notation "Second" => ConcreteSetup.backend ConcreteSetup.primeNodes
  (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Earlier" visible => CompleteCanonicalVerifier.earlier binary.description prime.description Nodes
  ConcreteSetup.primeNodes Repr Sh (Setup visible) (Cfg visible)
  (RuntimeStatement.binary_count binary prime.description prime.plan bounds.inputFits bounds.privateFits)
  (StrandMdocSetupSupport.metadata binary prime cantor scalars ids bounds visible)
local notation "Codec" visible => StrandCanonicalBackend.indexedCodec binary.description prime.description Nodes
  ConcreteSetup.primeNodes Repr Sh (Setup visible) (Cfg visible)
local notation "PrimePublic" visible => CanonicalRuntime.decodePrimePublic binary.description prime.description First Second Repr Sh
  (Setup visible) (CompleteCanonicalVerifier.basePublic binary.description prime.description Nodes
    ConcreteSetup.primeNodes Repr Sh (Setup visible) (Cfg visible))
  (RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits)

local notation "Budget" => 2+2*2443+(blocks+1)*List.length (Geometry.roles G)

def verify (visible : MdocSetupFamily.Values) (SHA : Strand.Oracle) (output : Output) : Bool :=
  StrandVerifier.verify binary.description prime.description First Second (Wire visible) (Earlier visible)
    (ProofBodyCodec.codec Repr G) (sample visible) (CanonicalRequest.hashPublic binary.nPublic)
    (PrimePublic visible) (fun (answer : Answer) => answer .batching) (Codec visible) SHA id output

def afterVerifier (visible : MdocSetupFamily.Values) (_context : Context) (output : Option Output) :
    Merkle.RandomOracle.Tree Bytes Digest Bool Budget :=
  StrandVerifierObserver.optional binary.description prime.description First Second (Wire visible) (Earlier visible)
    (ProofBodyCodec.codec Repr G) (sample visible) (Codec visible) id (CanonicalRequest.hashPublic binary.nPublic)
    (PrimePublic visible) (fun (answer : Answer) => answer .batching) output

/-- Both accepted and rejected results are the literal runtime decision
against the oracle seen by the observer, including its programmed leaves. -/
theorem verifier_result (visible : MdocSetupFamily.Values) (context : Context)
    (output : Option Output) (SHA : Strand.Oracle) :
    ((afterVerifier binary prime cantor scalars ids bounds sample visible context output).run SHA).1 =
      output.any (verify binary prime cantor scalars ids bounds sample visible SHA) :=
  StrandVerifierObserver.optional_result binary.description prime.description First Second (Wire visible) (Earlier visible)
    (ProofBodyCodec.codec Repr G) (sample visible) (Codec visible) id (CanonicalRequest.hashPublic binary.nPublic)
    (PrimePublic visible) (fun (answer : Answer) => answer .batching) output SHA

-- Probability transport uses the established view and support interfaces;
-- expanding an entire verifier tree or oracle-table enumeration is unnecessary.
attribute [local irreducible] afterVerifier MdocStrandZeroKnowledge.window
  MdocStrandZeroKnowledge.honest MdocStrandZeroKnowledge.simulate StatClose probOf

local notation "After" => afterVerifier (Context := Context) binary prime cantor scalars ids bounds sample
local notation "Window" => MdocStrandZeroKnowledge.window binary prime cantor scalars ids bounds before After
local notation "Real" => MdocStrandZeroKnowledge.honest binary prime cantor scalars ids bounds sample before requestOf After original remaining
local notation "Sim" => MdocStrandZeroKnowledge.simulate binary prime cantor scalars ids bounds sample before requestOf After
local notation "Epsilon" => (preQueries+Budget : ℕ)/(Fintype.card MerkleNonce : ℚ)
variable (pivotOne : binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
variable (independent : MdocWitness.HashNoninterference binary)
variable (valid : ∀ context,
  MdocStrandZeroKnowledge.Reachable binary prime cantor scalars ids bounds before context → MdocWitness.HashValid
  (RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context))
  (original (requestOf context)))
variable (signature : ∀ context,
  MdocStrandZeroKnowledge.Reachable binary prime cantor scalars ids bounds before context →
  let b := RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context)
  let p := RequestedSimulator.requestedPrime binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))
    (RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits) (requestOf context)
  p.circuit.Satisfies (CompleteHonest.primeInputs b p (original (requestOf context)) (remaining (requestOf context))))

include pivotOne primitive independent valid signature in
/-- Actual acceptance probabilities differ by at most the same privacy
error. No always-accepting simulator or acceptance certificate is assumed;
missing proofs and physical sampling failures remain rejecting outcomes. -/
theorem acceptance_probability (additional : Finset Bytes) (fallback : Strand.Oracle) :
    |probOf (fun coin : HonestCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        (Real coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)).2.1.2) (fun bit => bit = true) -
      probOf (fun coin : SimulatorCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        (Sim coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)).2.1.2) (fun bit => bit = true)| ≤ Epsilon := by
  have privacy := MdocStrandZeroKnowledge.statClose binary prime cantor scalars ids bounds sample before requestOf After
    original remaining pivotOne primitive independent valid signature additional fallback
  have compared := statClose_map (fun view => view.2.1.2) privacy
  unfold StatClose at compared
  exact compared (fun bit => bit = true)

end LfzkV2.Current.ZeroKnowledge.MdocStrandVerifierPrivacy
