import LfzkV2.Current.Mdoc.Soundness
import LfzkV2.Current.Mdoc.VerifierPrivacy
import LfzkV2.Current.Protocol.RustSampler

/-! The mdoc endpoints at the deployed challenge reader.

Each endpoint is stated for every reader of its kind: soundness for every
`Protocol.Sampler` (a reader with the balanced-fiber law), privacy and
completeness for every `Protocol.ExecutionSampler` (an executable reader,
with no law). The corollaries here fix the reader to the v2 Rust reader,
`Protocol.RustSampler.sampler`, at Rust's PRF counter limit, and take no
reader argument. Privacy and completeness modules do not import the
sampling laws; this module, which imports both, is where they meet. -/
noncomputable section
namespace LfzkV2.Current.Mdoc
open Application ApplicationSetup TranscriptV2

/-- The Rust challenge reader of a concrete mdoc setup. Its binary field is
GF(2^128), with the setup's packing basis as Rust's bit order. -/
abbrev Runtime.rustSampler {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
    (runtime : Mdoc.Runtime B) : Protocol.Sampler runtime.protocol Protocol.RustSampler.rustBlocks :=
  Protocol.RustSampler.sampler runtime.protocol rfl

namespace Soundness
open RuntimeAdaptive Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

/-- `averaged_ratio_le` at the Rust reader: the deployed soundness statement,
with no sampler premise. -/
theorem averaged_ratio_le_rust {fuel Q : ℕ}
    (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)
    (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
      (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)
    {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (external : Omega → Bytes → Digest)
    (adversary : Omega → Tree Bytes Digest (Mdoc.RuntimeSoundness.Request binary prime bounds × Bytes) fuel)
    (queryBound : ∀ coin oracle, (seen (adversary coin) oracle).card ≤ Q) (budget : Q < 2^127) :
    (∑ coin, density (event binary prime cantor scalars ids bounds (external coin) (adversary coin) fits
        (Mdoc.Setup.runtime binary prime cantor scalars (Mdoc.OracleSoundness.identifiers ids (external coin))
          bounds).rustSampler.data.sample)) / Fintype.card Omega ≤
      LfzkV2.Current.Soundness.Rate7.failureBound Q
        (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length :=
  averaged_ratio_le binary prime cantor scalars ids bounds fits bodyFits external adversary
    (fun coin => (Mdoc.Setup.runtime binary prime cantor scalars
      (Mdoc.OracleSoundness.identifiers ids (external coin)) bounds).rustSampler) queryBound budget

end Soundness

namespace ZeroKnowledge
open LfzkV2.Current.ZeroKnowledge ConcreteSetup Frontend LigeroFamily
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
attribute [local instance] StrandCanonicalHiding.columnFintype
  StrandCanonicalHiding.honestCoinsFintype StrandCanonicalHiding.publicCoinsFintype

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

/-- The Rust reader of every digest-selected setup, as an executable reader. -/
abbrev rust (visible : Mdoc.SetupFamily.Values) :
    Protocol.ExecutionSampler (Mdoc.SetupSupport.protocol binary prime cantor scalars ids bounds visible)
      Protocol.RustSampler.rustBlocks :=
  (Mdoc.SetupSupport.runtime binary prime cantor scalars ids bounds visible).rustSampler.data.execution

local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)
local notation "Private" => (CompleteHonest.Tape binary prime.description × CompleteHonest.Masks (B := B)) ×
  Backend.JointMasks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Public" => CompleteSimulation.Coins binary prime.description ×
  Backend.JointMasks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Auxiliary" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "HonestCoins" => Private × Auxiliary
local notation "SimulatorCoins" => Public × Auxiliary

variable {Context Observed : Type} {preQueries postQueries : ℕ}
variable (before : Mdoc.SetupFamily.Values → Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (after : Mdoc.SetupFamily.Values → Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
variable (original : Context → Fin binary.nPrivate → Bool)
variable (remaining : Context → Fin prime.description.remaining → Adapter.Mdoc.P)

local notation "Real" => honest binary prime cantor scalars ids bounds (rust binary prime cantor scalars ids bounds)
  before requestOf after original remaining
local notation "Sim" => simulate binary prime cantor scalars ids bounds (rust binary prime cantor scalars ids bounds)
  before requestOf after
local notation "Window" => window binary prime cantor scalars ids bounds before after
local notation "Epsilon" => (preQueries+postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ)

/-- `statClose` at the Rust reader: the deployed privacy statement, with no
sampler argument. -/
theorem statClose_rust
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ context, Reachable binary prime cantor scalars ids bounds before context → MdocWitness.HashValid
      (RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context))
      (original (context)))
    (signature : ∀ context, Reachable binary prime cantor scalars ids bounds before context →
      let b := RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context)
      let p := RequestedSimulator.requestedPrime binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))
        (RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits) (requestOf context)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original (context)) (remaining (context))))
    (additional : Finset Bytes) (fallback : Strand.Oracle) :
    StatClose Epsilon
      (fun coin : HonestCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Real coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback))
      (fun coin : SimulatorCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Sim coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)) :=
  statClose binary prime cantor scalars ids bounds (rust binary prime cantor scalars ids bounds)
    before requestOf after original remaining pivotOne primitive valid signature additional fallback

end ZeroKnowledge

namespace VerifierPrivacy
open LfzkV2.Current.ZeroKnowledge ConcreteSetup Frontend LigeroFamily Merkle.RandomOracle
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
attribute [local instance] StrandCanonicalHiding.honestCoinsFintype StrandCanonicalHiding.publicCoinsFintype

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "G" => MdocRuntime.geometry binary.description prime.description binary.plan prime.plan
local notation "Private" => (CompleteHonest.Tape binary prime.description × CompleteHonest.Masks (B := B)) ×
  Backend.JointMasks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Public" => CompleteSimulation.Coins binary prime.description ×
  Backend.JointMasks Nodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads)
local notation "Auxiliary" => (Fin 2443 → MerkleNonce) × (Fin 2443 → Digest)
local notation "HonestCoins" => Private × Auxiliary
local notation "SimulatorCoins" => Public × Auxiliary

variable {Context : Type} {preQueries : ℕ}
variable (before : Mdoc.SetupFamily.Values → Merkle.RandomOracle.Tree Bytes Digest Context preQueries)
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (original : Context → Fin binary.nPrivate → Bool)
variable (remaining : Context → Fin prime.description.remaining → Adapter.Mdoc.P)

local notation "Rust" => Mdoc.ZeroKnowledge.rust binary prime cantor scalars ids bounds
local notation "Budget" => 2+2*2443+(Protocol.RustSampler.rustBlocks+1)*List.length (Geometry.roles G)
local notation "After" => afterVerifier (Context := Context) binary prime cantor scalars ids bounds Rust
local notation "Window" => Mdoc.ZeroKnowledge.window binary prime cantor scalars ids bounds before After
local notation "Real" => Mdoc.ZeroKnowledge.honest binary prime cantor scalars ids bounds Rust before requestOf After original remaining
local notation "Sim" => Mdoc.ZeroKnowledge.simulate binary prime cantor scalars ids bounds Rust before requestOf After
local notation "Epsilon" => (preQueries+Budget : ℕ)/(Fintype.card MerkleNonce : ℚ)

/-- `acceptance_probability` at the Rust reader, with no sampler argument.
The verifier's raw-call budget counts the reader's `2^64 - 1` blocks per
boundary. -/
theorem acceptance_probability_rust
    (pivotOne : binary.basis 0 = 1)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (valid : ∀ context,
      Mdoc.ZeroKnowledge.Reachable binary prime cantor scalars ids bounds before context → MdocWitness.HashValid
      (RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context))
      (original (context)))
    (signature : ∀ context,
      Mdoc.ZeroKnowledge.Reachable binary prime cantor scalars ids bounds before context →
      let b := RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context)
      let p := RequestedSimulator.requestedPrime binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
        bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))
        (RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits) (requestOf context)
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original (context)) (remaining (context))))
    (additional : Finset Bytes) (fallback : Strand.Oracle) :
    |probOf (fun coin : HonestCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        (Real coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)).2.1.2) (fun bit => bit = true) -
      probOf (fun coin : SimulatorCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        (Sim coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)).2.1.2) (fun bit => bit = true)| ≤ Epsilon :=
  acceptance_probability binary prime cantor scalars ids bounds Rust before requestOf original remaining
    pivotOne primitive valid signature additional fallback

end VerifierPrivacy
end LfzkV2.Current.Mdoc
