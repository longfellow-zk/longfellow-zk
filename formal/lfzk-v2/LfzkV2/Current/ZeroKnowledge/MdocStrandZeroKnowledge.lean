import Bcs.OracleReachability
import LfzkV2.Current.ZeroKnowledge.StrandMdocSetupSupport
import LfzkV2.Current.ZeroKnowledge.StrandPrivacyBudget

/-! Complete numbered-strand mdoc privacy with public setup computed by the
same SHA oracle as the proof and both observers. The simulator has no
witness argument. Only opened leaf answers are programmed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocStrandZeroKnowledge
open Application ApplicationSetup ConcreteSetup Frontend TranscriptV2 LigeroFamily
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
attribute [local instance] StrandCanonicalHiding.columnFintype
  StrandCanonicalHiding.honestCoinsFintype StrandCanonicalHiding.publicCoinsFintype
attribute [local irreducible] MdocSetupFamily.setup MdocRuntime.geometry
  StrandCanonicalByteOracle.window StrandCanonicalByteSupport.window StrandMdocSetupSupport.window

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)
local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Answer" => MdocRuntime.Answer binary.description prime.description binary.plan prime.plan Nodes
local notation "Setup" visible => MdocSetupFamily.setup binary prime cantor scalars ids bounds visible
local notation "Values" SHA => MdocSetupFamily.values binary prime cantor scalars ids bounds SHA
local notation "Meta" SHA => MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA
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
local notation "Metadata" => CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := Answer) Sh binary.nPublic

variable {Context Observed : Type} {preQueries postQueries blocks : ℕ}
local notation "PublicView" => (Context × List (Bytes × Digest)) × (Option Output × Observed) × List (Bytes × Digest)
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
variable (after : MdocSetupFamily.Values → Context → Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))) →
  Merkle.RandomOracle.Tree Bytes Digest Observed postQueries)
variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (RuntimeStatement.degreeFits binary)) binary.nPublic → Fin prime.description.remaining → Adapter.Mdoc.P)

private def honestAt (visible : MdocSetupFamily.Values) (metadata : Metadata)
    (coins : HonestCoins) (SHA : Strand.Oracle) : PublicView :=
  StrandCanonicalHiding.rawReal binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
    (Setup visible) metadata original remaining (sample visible) (fun (answer : Answer) => answer .batching)
    (before visible) requestOf (after visible) coins SHA

private def simulateAt (visible : MdocSetupFamily.Values) (metadata : Metadata)
    (coins : SimulatorCoins) (SHA : Strand.Oracle) : PublicView :=
  StrandCanonicalHiding.rawSimulate binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
    (Setup visible) metadata (sample visible) (fun (answer : Answer) => answer .batching)
    (before visible) requestOf (after visible) coins SHA

/-- Literal honest execution, with public setup and metadata derived from
its one oracle. Auxiliary ghost labels are unused by the honest prover. -/
def honest (coins : HonestCoins) (SHA : Strand.Oracle) : PublicView :=
  honestAt binary prime cantor scalars ids bounds sample before requestOf after original remaining
    (Values SHA) (Meta SHA) coins SHA

/-- One witness-free simulator, using the same public setup derivation and
raw oracle as the observer. It never programs transcript or final-seal answers. -/
def simulate (coins : SimulatorCoins) (SHA : Strand.Oracle) : PublicView :=
  simulateAt binary prime cantor scalars ids bounds sample before requestOf after
    (Values SHA) (Meta SHA) coins SHA

local notation "Real" => honest binary prime cantor scalars ids bounds sample before requestOf after original remaining
local notation "Sim" => simulate binary prime cantor scalars ids bounds sample before requestOf after
local notation "Leaves" => StrandMdocSetup.leafWindow binary prime cantor scalars ids bounds
local notation "Epsilon" => (preQueries+postQueries : ℕ) / (Fintype.card MerkleNonce : ℚ)

/-- A fixed union covers every digest-selected setup and observer program.
It is chosen before sampling, rather than from an observed execution. -/
def window : Finset Bytes := Leaves ∪ ((Finset.univ.biUnion fun visible =>
  StrandCanonicalByteOracle.window binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
    (Setup visible) (before visible) (after visible)) ∪ StrandMdocSetupSupport.window binary prime cantor scalars)

local notation "Window" => window binary prime cantor scalars ids bounds before after

/-- Contexts returned by the actual observer family with public setup
computed from that same oracle. Unreachable policy branches impose no witness condition. -/
def Reachable (context : Context) : Prop :=
  Bcs.OracleReachability.FamilyReturns
    (MdocSetupFamily.values binary prime cantor scalars ids bounds) before context

theorem setup_subset : StrandMdocSetupSupport.window binary prime cantor scalars ⊆ Window := by
  intro raw member
  change raw ∈ Leaves ∪ (_ ∪ _)
  simp only [Finset.mem_union]
  exact Or.inr (Or.inr member)

theorem protocol_subset (visible : MdocSetupFamily.Values) :
    StrandCanonicalByteOracle.window binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
      (Setup visible) (before visible) (after visible) ⊆ Window := by
  intro raw member
  change raw ∈ Leaves ∪ ((Finset.univ.biUnion fun visible : MdocSetupFamily.Values =>
    StrandCanonicalByteOracle.window binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
      (Setup visible) (before visible) (after visible)) ∪ _)
  simp only [Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and]
  exact Or.inr (Or.inl ⟨visible,member⟩)

/-- Setup and metadata are included in the derived support, rather than
being fixed by an additional execution assumption. -/
theorem real_congr (coins : HonestCoins) (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw) : Real coins first = Real coins second := by
  have values := StrandMdocSetupSupport.values_congr binary prime cantor scalars ids bounds first second
    (fun raw member => same raw (setup_subset binary prime cantor scalars ids bounds before after member))
  have metadata := StrandMdocSetupSupport.metadata_congr binary prime cantor scalars ids bounds first second values
  unfold honest
  rw [values,metadata]
  unfold honestAt
  apply StrandCanonicalByteSupport.rawReal_congr binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
    (Setup (Values second)) (Meta second) original remaining (sample (Values second)) (fun (answer : Answer) => answer .batching)
    (before (Values second)) requestOf (after (Values second)) coins first second
  intro raw member
  apply same raw
  apply protocol_subset binary prime cantor scalars ids bounds before after (Values second)
  rw [StrandCanonicalByteOracle.window]
  simp only [Finset.mem_union]
  exact Or.inr member

/-- The public simulator, including its leaf programming and failure views,
depends on exactly the same fixed public support as the real experiment. -/
theorem simulate_congr (coins : SimulatorCoins) (first second : Strand.Oracle)
    (same : ∀ raw ∈ Window, first raw = second raw) : Sim coins first = Sim coins second := by
  have values := StrandMdocSetupSupport.values_congr binary prime cantor scalars ids bounds first second
    (fun raw member => same raw (setup_subset binary prime cantor scalars ids bounds before after member))
  have metadata := StrandMdocSetupSupport.metadata_congr binary prime cantor scalars ids bounds first second values
  unfold simulate
  rw [values,metadata]
  unfold simulateAt
  apply StrandCanonicalByteSupport.rawSimulate_congr binary prime.description prime.plan Nodes scalars bounds.inputFits bounds.privateFits
    (Setup (Values second)) (Meta second) (sample (Values second)) (fun (answer : Answer) => answer .batching)
    (before (Values second)) requestOf (after (Values second)) coins first second
  intro raw member
  apply same raw
  apply protocol_subset binary prime cantor scalars ids bounds before after (Values second)
  rw [StrandCanonicalByteOracle.window]
  simp only [Finset.mem_union]
  exact Or.inr member

theorem real_extend (coins : HonestCoins) (SHA outside : Strand.Oracle) :
    Real coins (OracleWindow.extend Window (fun raw => SHA raw.val) outside) = Real coins SHA := by
  apply real_congr binary prime cantor scalars ids bounds sample before requestOf after original remaining coins
  intro raw member
  exact OracleWindow.extend_mem Window _ outside raw member

theorem simulate_extend (coins : SimulatorCoins) (SHA outside : Strand.Oracle) :
    Sim coins (OracleWindow.extend Window (fun raw => SHA raw.val) outside) = Sim coins SHA := by
  apply simulate_congr binary prime cantor scalars ids bounds sample before requestOf after coins
  intro raw member
  exact OracleWindow.extend_mem Window _ outside raw member

variable (pivotOne : binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
variable (separated : MdocWitness.ReadDisjoint binary)
variable (valid : ∀ context, Reachable binary prime cantor scalars ids bounds before context → MdocWitness.HashValid
  (RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context))
  (original (requestOf context)))
variable (signature : ∀ context, Reachable binary prime cantor scalars ids bounds before context →
  let b := RequestedSimulator.requestedBinary binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) (requestOf context)
  let p := RequestedSimulator.requestedPrime binary prime.description prime.plan (MdocRuntime.shape binary.description prime.description binary.plan prime.plan
    bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary))
    (RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits) (requestOf context)
  p.circuit.Satisfies (CompleteHonest.primeInputs b p (original (requestOf context)) (remaining (requestOf context))))

include pivotOne primitive separated valid signature in
/-- Fixing the complement fixes setup, not the observer's protocol answers.
Averaging all leaf coordinates for the chosen setup adds no privacy loss. -/
theorem fixedComplement (outside : Strand.Oracle) :
    StatClose Epsilon
      (fun coin : HonestCoins × ({raw // raw ∈ Leaves} → Digest) => Real coin.1 (OracleWindow.extend Leaves coin.2 outside))
      (fun coin : SimulatorCoins × ({raw // raw ∈ Leaves} → Digest) => Sim coin.1 (OracleWindow.extend Leaves coin.2 outside)) := by
  let visible := Values outside
  let cfg := StrandCanonicalFullCoupling.configuration binary prime.description prime.plan Nodes scalars
    bounds.inputFits bounds.privateFits (Setup visible)
  let codec := StrandCanonicalBackend.indexedCodec binary.description prime.description Nodes ConcreteSetup.primeNodes
    Repr Sh (Setup visible) cfg
  let dec := StrandCanonicalBackend.indexedDecoders binary.description prime.description Nodes ConcreteSetup.primeNodes
    Repr Sh (Setup visible) cfg
  let encode := StrandGhostMerkle.Probability.leafEmbedding codec dec
  have encodeDomain : ∀ leaf, SHAOracle.merkleDomain (encode leaf) := by
    intro leaf
    exact SHAOracle.leaf_in_domain _ _ _ _ _ _ (by decide) leaf
  have localSubset : StrandLeafWindow.window encode ⊆ Leaves :=
    StrandMdocSetup.leaves_subset binary prime cantor scalars ids bounds visible
  have leafDomain := StrandMdocSetup.leafWindow_domain binary prime cantor scalars ids bounds
  have law := StrandLeafWindow.statClose_of_extension encode
    (honestAt binary prime cantor scalars ids bounds sample before requestOf after original remaining visible (Meta outside))
    (simulateAt binary prime cantor scalars ids bounds sample before requestOf after visible (Meta outside))
    Leaves localSubset Epsilon (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) outside (by
      intro complementTable
      let complement := OracleWindow.extend Leaves complementTable outside
      have complementValues : (Values complement) = visible :=
        StrandMdocSetup.values_extend binary prime cantor scalars ids bounds Leaves leafDomain complementTable outside
      have reached (table : _ → Digest) : Reachable binary prime cantor scalars ids bounds before
          ((before visible).run (StrandGhostMerkle.Swap.Slice.oracle encode complement table)).1 := by
        have valuesEqual : (Values (StrandGhostMerkle.Swap.Slice.oracle encode complement table)) = visible :=
          (StrandMdocSetup.values_leafOracle binary prime cantor scalars ids bounds encode
            encodeDomain table complement).trans
              complementValues
        exact Bcs.OracleReachability.familyReturns_of_setup
          (MdocSetupFamily.values binary prime cantor scalars ids bounds) before
          (StrandGhostMerkle.Swap.Slice.oracle encode complement table) visible valuesEqual
      apply StrandCanonicalHiding.raw_fixedComplement binary prime.description prime.plan Nodes scalars
        bounds.inputFits bounds.privateFits (Setup visible) (Meta outside) original remaining (sample visible)
        (fun (answer : Answer) => answer .batching) (before visible) requestOf (after visible)
        complement pivotOne primitive
      · intro table
        exact MdocWitness.uniformHashValid_of_valid
          ((MdocWitness.noninterference_of_readDisjoint binary separated).with_publicBits (requestOf ((before visible).run
            (StrandGhostMerkle.Swap.Slice.oracle encode complement table)).1).publicBits)
          _ (valid _ (reached table))
      · intro table
        exact signature _ (reached table))
  apply Probability.changeFintype (statClose_reindex (Equiv.refl _) (Equiv.refl _) ?_ ?_ law)
  · intro coin
    unfold honest
    rw [StrandMdocSetup.values_extend binary prime cantor scalars ids bounds Leaves
        (StrandMdocSetup.leafWindow_domain binary prime cantor scalars ids bounds) coin.2 outside,
      StrandMdocSetup.metadata_extend binary prime cantor scalars ids bounds Leaves
        (StrandMdocSetup.leafWindow_domain binary prime cantor scalars ids bounds) coin.2 outside]
    rfl
  · intro coin
    unfold simulate
    rw [StrandMdocSetup.values_extend binary prime cantor scalars ids bounds Leaves
        (StrandMdocSetup.leafWindow_domain binary prime cantor scalars ids bounds) coin.2 outside,
      StrandMdocSetup.metadata_extend binary prime cantor scalars ids bounds Leaves
        (StrandMdocSetup.leafWindow_domain binary prime cantor scalars ids bounds) coin.2 outside]
    rfl

include pivotOne primitive separated valid signature in
/-- End-to-end mdoc statistical privacy under one shared SHA random oracle,
including oracle-derived public setup, an adaptive request, both original raw
observer traces, authentication, and the complete-proof final seal. -/
theorem statClose (additional : Finset Bytes) (fallback : Strand.Oracle) :
    StatClose Epsilon
      (fun coin : HonestCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Real coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback))
      (fun coin : SimulatorCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Sim coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)) := by
  exact Probability.changeFintype (SHAOracleWindowProbability.window_statClose Leaves (Window ∪ additional)
    (Finset.subset_union_left.trans Finset.subset_union_left)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) fallback Real Sim
    (fun outside => fixedComplement binary prime cantor scalars ids bounds sample before requestOf after original remaining
      pivotOne primitive separated valid signature outside))

include pivotOne primitive separated valid signature in
/-- With at most 2^128 raw observer calls in total, the complete ideal-oracle
view has statistical distance at most 2^-128. This is a statement about the
oracle model, not a numerical claim about concrete SHA-256. -/
theorem statClose_at_query_budget (additional : Finset Bytes) (fallback : Strand.Oracle)
    (budget : preQueries+postQueries ≤ 2^128) :
    StatClose (1/(2:ℚ)^128)
      (fun coin : HonestCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Real coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback))
      (fun coin : SimulatorCoins × ({raw // raw ∈ Window ∪ additional} → Digest) =>
        Sim coin.1 (OracleWindow.extend (Window ∪ additional) coin.2 fallback)) := by
  exact (statClose binary prime cantor scalars ids bounds sample before requestOf after original remaining
    pivotOne primitive separated valid signature additional fallback).mono
    (StrandPrivacyBudget.at_query_budget preQueries postQueries budget)

end LfzkV2.Current.ZeroKnowledge.MdocStrandZeroKnowledge
