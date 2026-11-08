import LfzkV2.Current.ZeroKnowledge.MdocOracleWindows
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeGlobalCoins
import LfzkV2.Current.ZeroKnowledge.FrontendRuntimeStatement
import LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment
import LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability
import LfzkV2.Current.ZeroKnowledge.Error
import LfzkV2.Current.ZeroKnowledge.MdocContextPrivacy

/-! The complete rate-1/7 mdoc privacy experiments. The public setup,
causal metadata, Merkle authentication, and observer all use one SHA
oracle. The stateful observer receives the complete proof and retains its
private context and both original raw query traces. The simulator has no
witness argument. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocZeroKnowledge
open Application ApplicationSetup ConcreteSetup Frontend Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] StatClose probOf
attribute [local instance] BackendRuntime.requestFintype BackendRuntime.leafFintype
  BackendRuntime.frontCoinsFintype BackendRuntime.genericBackendMasksFintype
  BackendRuntime.backendMasksFintype BackendRuntime.merkleCoinsFintype BackendRuntime.coinsFintype

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Answer" => MdocRuntime.Answer binary.description prime.description binary.plan prime.plan Nodes
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Setup" SHA => MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
local notation "Cfg" SHA => MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA
local notation "Meta" SHA => MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA
local notation "bCount" => RuntimeStatement.binary_count binary prime.description prime.plan bounds.inputFits bounds.privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits

variable {Context Observed : Type} {preM preT postM postT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic)
variable (priorFamily : MdocSetupFamily.Values → RandomOracle.TwoOracleTree Bytes Digest Bytes
  (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
  Context preM preT)
variable (afterFamily : MdocSetupFamily.Values → Context → Option (MdocOracleWindows.Output binary prime bounds) →
  RandomOracle.TwoOracleTree Bytes Digest Bytes
    (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    Observed postM postT)
variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

abbrev TranscriptTable :=
  {raw // raw ∈ MdocOracleWindows.transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits} →
    Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor)

abbrev HonestCoins :=
  BackendRuntimeGlobalCoins.PrivateProver (C := Answer) binary prime.description Nodes ×
    TranscriptTable binary prime cantor scalars ids bounds priorFamily afterFamily fits

abbrev SimulatorCoins :=
  BackendRuntimeGlobalCoins.PublicProver (C := Answer) binary prime.description Nodes ×
    TranscriptTable binary prime cantor scalars ids bounds priorFamily afterFamily fits

variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin prime.description.remaining → Adapter.Mdoc.P)

/-- The literal honest prover, including terminal authentication and the
normal final-seal query. Unused auxiliary coins do not enter its tape. -/
def honest (coin : HonestCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits)
    (SHA : Bytes → Digest) :
    Observer.View Bytes Digest Bytes (Digest × Answer) Context
      (Option (MdocOracleWindows.Output binary prime bounds)) Observed :=
  RequestedContextExperiment.rawHonest binary prime.description prime.plan Nodes Repr Sh (Setup SHA) (Cfg SHA)
    bCount pCount (Meta SHA) (MdocPublicSetup.draw binary prime cantor scalars ids bounds SHA)
    requestOf (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))
    (afterFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA)) fits
    (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) original remaining
    (BackendRuntimeGlobalCoins.honestTape binary prime.description Nodes (coin.1,())) SHA
    (OracleWindow.extend
      (MdocOracleWindows.transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits)
      coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))

/-- One public simulator for every valid witness. Only the public setup,
observer programs, oracle, and independent simulator coins are arguments. -/
def simulate (coin : SimulatorCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits)
    (SHA : Bytes → Digest) :
    Observer.View Bytes Digest Bytes (Digest × Answer) Context
      (Option (MdocOracleWindows.Output binary prime bounds)) Observed :=
  RequestedContextExperiment.rawSimulated binary prime.description prime.plan Nodes Repr Sh (Setup SHA) (Cfg SHA)
    bCount pCount (Meta SHA) (MdocPublicSetup.draw binary prime cantor scalars ids bounds SHA)
    requestOf (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))
    (afterFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA)) fits
    (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)
    (BackendRuntimeGlobalCoins.simulatorTape binary prime.description Nodes (coin.1,())) SHA
    (OracleWindow.extend
      (MdocOracleWindows.transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits)
      coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))

attribute [local irreducible] honest simulate

private def exchangeTables {Prover First Second : Type} :
    ((Prover × First) × Second) ≃ ((Prover × Second) × First) where
  toFun coin := ((coin.1.1,coin.2),coin.1.2)
  invFun coin := ((coin.1.1,coin.2),coin.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

local notation "V" => MdocOracleWindows.merkleWindow binary prime cantor scalars bounds priorFamily afterFamily
local notation "Epsilon" =>
  2*MerklePreparation.error (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 preM +
    MerkleSimulation.openingError (Fintype.card MerkleNonce) (Fintype.card Digest)
      2443 (2443-84) postM + (preT:ℚ)/(2:ℚ)^46208

variable (pivotOne : binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

include pivotOne primitive bodyFits in
/-- The complete factories are evaluated at the actual shared SHA oracle.
The complementary slice may determine setup, the observer's program, and
its selected public request. Only actually reachable requests need valid
witnesses; no frontend/backend execution certificate is supplied. -/
theorem fixedComplement (outside : Bytes → Digest)
    (valid : ∀ request,
      MdocContextPrivacy.RawReachable binary prime cantor bounds requestOf
        (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds outside)) outside request →
      MdocContextPrivacy.ValidWitness binary prime bounds original remaining request) :
    StatClose Epsilon
      (fun coin : HonestCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V} → Digest) =>
        honest binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits original remaining
          coin.1 (OracleWindow.extend V coin.2 outside))
      (fun coin : SimulatorCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V} → Digest) =>
        simulate binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits
          coin.1 (OracleWindow.extend V coin.2 outside)) := by
  have law := MdocContextPrivacy.family binary prime cantor scalars ids bounds original remaining requestOf outside fits
    priorFamily afterFamily pivotOne primitive valid bodyFits
  apply Probability.changeFintype (statClose_reindex exchangeTables exchangeTables ?_ ?_ law)
  · intro coin
    unfold honest MdocPublicSetup.configuration MdocPublicSetup.draw
    rw [MdocContextPrivacy.setup_extend binary prime cantor scalars ids bounds outside V
        (MdocOracleWindows.merkle_domain binary prime cantor scalars bounds priorFamily afterFamily) coin.2,
      MdocContextPrivacy.metadata_extend binary prime cantor scalars ids bounds outside V
        (MdocOracleWindows.merkle_domain binary prime cantor scalars bounds priorFamily afterFamily) coin.2,
      MdocOracleWindows.values_extend binary prime cantor scalars ids bounds priorFamily afterFamily outside coin.2]
    rfl
  · intro coin
    unfold simulate MdocPublicSetup.configuration MdocPublicSetup.draw
    rw [MdocContextPrivacy.setup_extend binary prime cantor scalars ids bounds outside V
        (MdocOracleWindows.merkle_domain binary prime cantor scalars bounds priorFamily afterFamily) coin.2,
      MdocContextPrivacy.metadata_extend binary prime cantor scalars ids bounds outside V
        (MdocOracleWindows.merkle_domain binary prime cantor scalars bounds priorFamily afterFamily) coin.2,
      MdocOracleWindows.values_extend binary prime cantor scalars ids bounds priorFamily afterFamily outside coin.2]
    rfl

include pivotOne primitive bodyFits in
/-- End-to-end statistical zero knowledge for the complete mdoc runtime
in the ideal-oracle model. For any distinguishing event, the difference
between its real and simulated probabilities is at most the displayed
bound. The one simulator above works for every fixed valid witness map.

Any additional finite SHA marginal is sampled jointly with the mandatory
Merkle marginal. Thus setup hashes, metadata hashes, and raw observer
queries may share the oracle. No conditioning on an observed trace or
independence of a setup-derived identifier is assumed. Private observer
state is arbitrary, and both complete raw query traces remain observable. -/
theorem statClose (additionalSHA : Finset Bytes) (fallback : Bytes → Digest)
    (valid : ∀ (outside : Bytes → Digest) request,
      MdocContextPrivacy.RawReachable binary prime cantor bounds requestOf
        (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds outside)) outside request →
      MdocContextPrivacy.ValidWitness binary prime bounds original remaining request) :
    StatClose
      ((47745992+4886*(preM:ℚ)+4718*(postM:ℚ))/(2:ℚ)^320 +
        47716680/(2:ℚ)^256 +
        4884*(preM:ℚ)/(2:ℚ)^512 + (preT:ℚ)/(2:ℚ)^46208)
      (fun coin : HonestCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V ∪ additionalSHA} → Digest) =>
        honest binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits original remaining
          coin.1 (OracleWindow.extend (V ∪ additionalSHA) coin.2 fallback))
      (fun coin : SimulatorCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V ∪ additionalSHA} → Digest) =>
        simulate binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits
          coin.1 (OracleWindow.extend (V ∪ additionalSHA) coin.2 fallback)) := by
  have nonnegative : 0 ≤ Epsilon := by
    have merkle := Error.nonnegative (Fintype.card MerkleNonce) (Fintype.card Digest) 2 2443 84 preM postM 0
    simp only [Error.bound,Nat.cast_zero,zero_div,add_zero] at merkle
    exact add_nonneg merkle (by positivity)
  have law := SHAOracleWindowProbability.window_statClose V (V ∪ additionalSHA)
    Finset.subset_union_left nonnegative fallback
    (honest binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits original remaining)
    (simulate binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits)
    (fun outside => fixedComplement binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits
      original remaining pivotOne primitive bodyFits outside (valid outside))
  rw [Error.rate7_protocol] at law
  exact Probability.changeFintype law

include pivotOne primitive bodyFits in
/-- The complete ideal-oracle privacy theorem at the concrete 2^128-query
budget, including both earlier and later SHA queries and the transcript term. -/
theorem statClose_at_query_budget (additionalSHA : Finset Bytes) (fallback : Bytes → Digest)
    (valid : ∀ (outside : Bytes → Digest) request,
      MdocContextPrivacy.RawReachable binary prime cantor bounds requestOf
        (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds outside)) outside request →
      MdocContextPrivacy.ValidWitness binary prime bounds original remaining request)
    (merkleQueries : preM+postM ≤ 2^128) (transcriptQueries : preT ≤ 2^128) :
    StatClose
      (1/(2:ℚ)^179)
      (fun coin : HonestCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V ∪ additionalSHA} → Digest) =>
        honest binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits original remaining
          coin.1 (OracleWindow.extend (V ∪ additionalSHA) coin.2 fallback))
      (fun coin : SimulatorCoins binary prime cantor scalars ids bounds priorFamily afterFamily fits ×
          ({raw // raw ∈ V ∪ additionalSHA} → Digest) =>
        simulate binary prime cantor scalars ids bounds requestOf priorFamily afterFamily fits
          coin.1 (OracleWindow.extend (V ∪ additionalSHA) coin.2 fallback)) := by
  apply StatClose.mono _ (statClose binary prime cantor scalars ids bounds requestOf
    priorFamily afterFamily fits original remaining pivotOne primitive bodyFits additionalSHA fallback valid)
  have budget := Error.rate7_at_query_budget preM postM preT merkleQueries transcriptQueries
  rw [Error.rate7] at budget
  exact budget.le

end LfzkV2.Current.ZeroKnowledge.MdocZeroKnowledge
