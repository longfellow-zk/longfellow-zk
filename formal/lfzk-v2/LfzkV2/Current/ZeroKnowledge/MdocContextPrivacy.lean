import LfzkV2.Current.ZeroKnowledge.MdocWitness
import LfzkV2.Current.ZeroKnowledge.MdocOracleWindows
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobalProof
import LfzkV2.Current.ZeroKnowledge.RequestedContextProbability

/-! Concrete rate-1/7 privacy for the stateful mdoc observer. Application
truth is required only for a public request selected by an actual oracle
execution. The trusted hash relation and signature-circuit satisfaction
discharge every runtime row and frontend validity premise. In particular,
there is no supplied execution, backend-layout, or per-round certificate.

The final finite marginals are generated from the actual public-setup
family and arbitrary raw observer programs. Private observer states need
not form a finite type: their common finite support is derived from the
bounded query programs and finite oracle answers. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocContextPrivacy
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] StatClose probOf
attribute [local irreducible] BackendRuntime.hashChecks FullCoupling.hashChecks
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run
attribute [local instance] BackendRuntime.requestFintype BackendRuntime.leafFintype
  BackendRuntime.frontCoinsFintype BackendRuntime.genericBackendMasksFintype
  BackendRuntime.backendMasksFintype BackendRuntime.merkleCoinsFintype BackendRuntime.coinsFintype
  OracleHonestCoins.frameFintype

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

private instance circuitNonempty {F : Type} [Field F] {out input : ℕ}
    (circuit : Layered.Circuit F out input) : Nonempty (CircuitTape circuit) := by
  induction circuit with
  | input => infer_instance
  | entry _ _ _ ih => exact ih
  | layer _ _ _ ih =>
      obtain ⟨tail⟩ := ih
      exact ⟨((fun _ => ⟨0,0⟩),(0,0,0)),tail⟩

private instance profileNonempty {F : Type} [Field F] (nodes : Fin 2792 ↪ F) (cells : ℕ) :
    Nonempty (Backend.ProfileTape nodes cells) := ⟨((0,0,0),0,0)⟩

private instance honestNonempty : Nonempty (CompleteHonest.Tape binary prime.description) :=
  Nonempty.map (GlobalCoins.tapeEquiv binary prime.description).symm inferInstance

private instance simulationNonempty : Nonempty (CompleteSimulation.Coins binary prime.description) :=
  Nonempty.map (GlobalCoins.coinsEquiv binary prime.description) inferInstance

local notation "Sh" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
  (by change 128 < 2^64; decide)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Answer" => MdocRuntime.Answer binary.description prime.description binary.plan prime.plan Nodes
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Setup" SHA => MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
local notation "Cfg" SHA => MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA
local notation "Meta" SHA => MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA
local notation "bCount" => RuntimeStatement.binary_count binary prime.description prime.plan bounds.inputFits bounds.privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime.description prime.plan bounds.inputFits bounds.privateFits

variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic → Fin prime.description.remaining → Adapter.Mdoc.P)

/-- Ordinary application truth for the fixed witness associated with a
public request. Generated adapter and backend equations are conclusions. -/
def ValidWitness (request : Request) : Prop :=
  MdocWitness.HashValid (RequestedSimulator.requestedBinary binary prime.description prime.plan Sh request) (original request) ∧
    let b := RequestedSimulator.requestedBinary binary prime.description prime.plan Sh request
    let p := RequestedSimulator.requestedPrime binary prime.description prime.plan Sh pCount request
    p.circuit.Satisfies (CompleteHonest.primeInputs b p (original request) (remaining request))

variable {Context Observed : Type} {preM preT postM postT : ℕ}
variable (requestOf : Context → CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide)) binary.nPublic)
variable (prior : RandomOracle.TwoOracleTree Bytes Digest Bytes
  (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
  Context preM preT)
variable (after : Context → Option (MdocOracleWindows.Output binary prime bounds) →
  RandomOracle.TwoOracleTree Bytes Digest Bytes
    (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    Observed postM postT)
variable (outside : Bytes → Digest)

/-- Only requests returned by a consistent execution need witnesses.
Arbitrary malformed and repeated raw queries are allowed in that execution. -/
def RawReachable (request : Request) : Prop :=
  ∃ (inside : Bytes → Digest) (HT : Bytes → Digest × Answer),
    requestOf (Observer.run (SHAOracle.merge SHAOracle.merkleDomain outside inside) HT prior).1 = request

variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

omit [DecidableEq B] in
theorem reachable_raw (complement : Bytes → Digest × Answer) (request : Request)
    (reachable : BackendRuntimeContext.RequestReachable binary prime.description prime.plan Repr Sh (Setup outside)
      requestOf ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement prior) outside request) :
    RawReachable binary prime cantor bounds requestOf prior outside request := by
  obtain ⟨inside,H,selected⟩ := reachable
  refine ⟨inside,(MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).oracle complement H,?_⟩
  have readback := TranscriptObserver.program_output
    (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside) complement
    (SHAOracle.merge SHAOracle.merkleDomain outside inside) H prior
  exact (congrArg requestOf readback).symm.trans selected

section FiniteContext
variable [Fintype Context]
variable (pivotOne : binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
variable (valid : ∀ request, RawReachable binary prime cantor bounds requestOf prior outside request →
  ValidWitness binary prime bounds original remaining request)
variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

include pivotOne primitive valid bodyFits in
/-- Specialize the complete typed protocol theorem to ordinary mdoc
witnesses. The lower-level mathematical window can be chosen before the
concrete observer-family marginal is installed below. -/
theorem typed (complement : Bytes → Digest × Answer) (large : Finset Bytes)
    (contains : BackendRuntimeContext.window binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside)
      ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement prior)
      (fun context proof => (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement (after context proof)) outside ⊆ large)
    (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM + (preT : ℚ)/(2 : ℚ)^46208)
      (BackendRuntimeContextGlobal.honest binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        requestOf ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement prior)
        (fun context proof => (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement (after context proof))
        outside (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) original remaining large)
      (BackendRuntimeContextGlobal.simulate binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        requestOf ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement prior)
        (fun context proof => (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement (after context proof))
        outside (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) large) := by
  apply BackendRuntimeContextGlobal.statClose binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
    requestOf _ _ outside (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) original remaining large contains onlyMerkle pivotOne
  · intro H earlier labels reachable
    have ordinary := valid (requestOf earlier.1)
      (reachable_raw binary prime cantor scalars ids bounds requestOf prior outside fits complement _ reachable)
    exact MdocWitness.backend_hash binary prime cantor scalars ids bounds outside original H
      (BackendRuntime.publicPrefix binary prime.description prime.plan Repr Sh (Setup outside) requestOf earlier) labels ordinary.1
  · exact fits
  · exact bodyFits
  · intro H coins earlier labels reachable
    have ordinary := valid (requestOf earlier.1)
      (reachable_raw binary prime cantor scalars ids bounds requestOf prior outside fits complement _ reachable)
    exact MdocWitness.satisfied binary prime cantor scalars ids bounds outside original remaining H coins
      (BackendRuntime.publicPrefix binary prime.description prime.plan Repr Sh (Setup outside) requestOf earlier) labels pivotOne primitive ordinary.1 ordinary.2

include pivotOne primitive valid bodyFits in
/-- The raw transcript marginal retains all observer queries and the
returned programmed oracle. Its statistical premise is the derived
complete protocol theorem, not an assumed simulator certificate. -/
theorem raw (large transcript : Finset Bytes)
    (contains : ∀ complement : Bytes → Digest × Answer,
      BackendRuntimeContext.window binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside)
        ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement prior)
        (fun context proof => (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).program complement (after context proof)) outside ⊆ large)
    (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)
    (covers : ∀ point : {point : QueryRuntime.Runtime.Point Repr Sh (Setup outside) binary.nPublic //
      QueryRuntime.Runtime.Canonical Repr Sh (Setup outside) binary.nPublic point},
      (MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).encode point ∈ transcript) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM + (preT : ℚ)/(2 : ℚ)^46208)
      (fun coin : (BackendRuntimeGlobalCoins.PrivateProver (C := Answer) binary prime.description Nodes ×
          ({raw // raw ∈ large} → Digest)) × ({raw // raw ∈ transcript} → Digest × Answer) =>
        RequestedContextExperiment.rawHonest binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
          (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf prior after fits
          (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) original remaining
          (BackendRuntimeGlobalCoins.honestTape binary prime.description Nodes coin.1)
          (OracleWindow.extend large coin.1.2 outside)
          (OracleWindow.extend transcript coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)))
      (fun coin : (BackendRuntimeGlobalCoins.PublicProver (C := Answer) binary prime.description Nodes ×
          ({raw // raw ∈ large} → Digest)) × ({raw // raw ∈ transcript} → Digest × Answer) =>
        RequestedContextExperiment.rawSimulated binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
          (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf prior after fits
          (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)
          (BackendRuntimeGlobalCoins.simulatorTape binary prime.description Nodes coin.1)
          (OracleWindow.extend large coin.1.2 outside)
          (OracleWindow.extend transcript coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))) := by
  letI : Nonempty Answer := ⟨(MdocProofRate7.defaultAnswer binary prime cantor).2⟩
  have positive : 0 ≤ (preT : ℚ)/(2 : ℚ)^46208 := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have nonnegative' : 0 ≤ 2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM + (preT : ℚ)/(2 : ℚ)^46208 := by
    have old := Error.nonnegative (Fintype.card Digest) (Fintype.card Digest) 2 2443 84 preM postM 0
    simp only [Error.bound,Nat.cast_zero,zero_div,add_zero] at old
    exact add_nonneg old positive
  refine RequestedContextProbability.window_statClose binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
    (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf prior after fits
    (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) bodyFits
    (BackendRuntimeGlobalCoins.honestTape binary prime.description Nodes)
    (BackendRuntimeGlobalCoins.simulatorTape binary prime.description Nodes)
    (fun coin => OracleWindow.extend large coin.2 outside)
    (fun coin => OracleWindow.extend large coin.2 outside) original remaining pivotOne ?_
    (MdocProofRate7.defaultAnswer binary prime cantor)
    (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) transcript covers nonnegative' ?_
  · intro coin H complement
    let HM := OracleWindow.extend large coin.2 outside
    let request := requestOf (Observer.run HM
      ((MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).oracle complement H) prior).1
    have merged : SHAOracle.merge SHAOracle.merkleDomain outside HM = HM :=
      BackendRuntimeContextGlobal.merge_oracle outside large onlyMerkle coin.2
    have reachable : RawReachable binary prime cantor bounds requestOf prior outside request := by
      refine ⟨HM,(MdocOracleWindows.byteCodec binary prime cantor scalars ids bounds fits outside).oracle complement H,?_⟩
      rw [merged]
    have ordinary := (valid request reachable).1
    unfold OracleHonestRefresh.hashChecks
    intro responses native converted
    apply MdocWitness.coupling_hash
    exact ordinary
  · intro complement
    have law := typed binary prime cantor scalars ids bounds original remaining requestOf prior after outside fits pivotOne primitive valid bodyFits
      complement large (contains complement) onlyMerkle
    unfold BackendRuntimeContextGlobal.honest BackendRuntimeContextGlobal.simulate BackendRuntimeContextGlobal.oracle at law
    exact Probability.changeFintype law

end FiniteContext

section Family
variable (priorFamily : MdocSetupFamily.Values → RandomOracle.TwoOracleTree Bytes Digest Bytes
  (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
  Context preM preT)
variable (afterFamily : MdocSetupFamily.Values → Context → Option (MdocOracleWindows.Output binary prime bounds) →
  RandomOracle.TwoOracleTree Bytes Digest Bytes
    (Digest × MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    Observed postM postT)

local notation "visible" => MdocSetupFamily.values binary prime cantor scalars ids bounds outside
local notation "Supported" => MdocOracleWindows.Support binary prime cantor priorFamily
local notation "V" => MdocOracleWindows.merkleWindow binary prime cantor scalars bounds priorFamily afterFamily
local notation "W" => MdocOracleWindows.transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits

variable (pivotOne : binary.basis 0 = 1)
variable (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
variable (familyValid : ∀ request, RawReachable binary prime cantor bounds requestOf
  (priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds outside)) outside request →
  ValidWitness binary prime bounds original remaining request)
variable (bodyFits : ProofBodyBounds.bodyBound (MdocRuntime.representations scalars)
  (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan) ≤ CanonicalPrefix.maxLength)

private theorem erase_honest_support (tape : HonestRuntime.Tape binary prime.description Nodes) (HM : Bytes → Digest) (HT : Bytes → Digest × Answer) :
    ObserverStateful.mapContext Subtype.val
      (RequestedContextExperiment.rawHonest binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) (requestOf ∘ Subtype.val) (MdocOracleWindows.supportedPrior binary prime cantor priorFamily visible) (MdocOracleWindows.supportedAfter binary prime cantor bounds priorFamily afterFamily visible) fits
        (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) original remaining tape HM HT) =
      RequestedContextExperiment.rawHonest binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf (priorFamily visible) (afterFamily visible) fits
        (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) original remaining tape HM HT := by
  unfold RequestedContextExperiment.rawHonest ObserverStatefulRaw.rawRun
  exact ObserverFamilySupport.supported_experiment priorFamily (fun _ => requestOf) (fun _ => _) afterFamily visible HM HT

private theorem erase_simulated_support (tape : CompleteSimulator.Tape (C := Answer) binary prime.description Nodes) (HM : Bytes → Digest) (HT : Bytes → Digest × Answer) :
    ObserverStateful.mapContext Subtype.val
      (RequestedContextExperiment.rawSimulated binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) (requestOf ∘ Subtype.val) (MdocOracleWindows.supportedPrior binary prime cantor priorFamily visible) (MdocOracleWindows.supportedAfter binary prime cantor bounds priorFamily afterFamily visible) fits
        (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) tape HM HT) =
      RequestedContextExperiment.rawSimulated binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
        (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf (priorFamily visible) (afterFamily visible) fits
        (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) tape HM HT := by
  unfold RequestedContextExperiment.rawSimulated ObserverStatefulRaw.rawRun
  exact ObserverFamilySupport.supported_experiment priorFamily (fun _ => requestOf) (fun _ => _) afterFamily visible HM HT

include pivotOne primitive familyValid bodyFits in
/-- The fixed outside-oracle bound for the actual raw mdoc prover and
simulator. Both oracle marginals and private-context enumeration are
constructed here; no coverage, backend or simulator certificate is an
argument. The original private context is retained in the final view. -/
theorem family :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM + (preT : ℚ)/(2 : ℚ)^46208)
      (fun coin : (BackendRuntimeGlobalCoins.PrivateProver (C := Answer) binary prime.description Nodes ×
          ({raw // raw ∈ V} → Digest)) × ({raw // raw ∈ W} → Digest × Answer) =>
        RequestedContextExperiment.rawHonest binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
          (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf (priorFamily visible) (afterFamily visible) fits
          (fun _ => MdocProofRate7.defaultAnswer binary prime cantor) original remaining
          (BackendRuntimeGlobalCoins.honestTape binary prime.description Nodes coin.1)
          (OracleWindow.extend V coin.1.2 outside)
          (OracleWindow.extend W coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)))
      (fun coin : (BackendRuntimeGlobalCoins.PublicProver (C := Answer) binary prime.description Nodes ×
          ({raw // raw ∈ V} → Digest)) × ({raw // raw ∈ W} → Digest × Answer) =>
        RequestedContextExperiment.rawSimulated binary prime.description prime.plan Nodes Repr Sh (Setup outside) (Cfg outside) bCount pCount (Meta outside)
          (MdocPublicSetup.draw binary prime cantor scalars ids bounds outside) requestOf (priorFamily visible) (afterFamily visible) fits
          (fun _ => MdocProofRate7.defaultAnswer binary prime cantor)
          (BackendRuntimeGlobalCoins.simulatorTape binary prime.description Nodes coin.1)
          (OracleWindow.extend V coin.1.2 outside)
          (OracleWindow.extend W coin.2 (fun _ => MdocProofRate7.defaultAnswer binary prime cantor))) := by
  have smallValid (request : Request)
      (reachable : RawReachable binary prime cantor bounds (requestOf ∘ Subtype.val)
        (MdocOracleWindows.supportedPrior binary prime cantor priorFamily visible) outside request) :
      ValidWitness binary prime bounds original remaining request := by
    obtain ⟨inside,H,selected⟩ := reachable
    apply familyValid request
    refine ⟨inside,H,?_⟩
    have erased := ObserverFamilySupport.restrict_run priorFamily visible (SHAOracle.merge SHAOracle.merkleDomain outside inside) H
    have erasedContext := congrArg Prod.fst erased
    dsimp only at erasedContext
    exact (congrArg requestOf erasedContext).symm.trans selected
  have finiteLaw := raw binary prime cantor scalars ids bounds original remaining
    (requestOf ∘ Subtype.val) (MdocOracleWindows.supportedPrior binary prime cantor priorFamily visible)
    (MdocOracleWindows.supportedAfter binary prime cantor bounds priorFamily afterFamily visible)
    outside fits pivotOne primitive smallValid bodyFits V W
    (fun complement => MdocOracleWindows.backend_window_contains binary prime cantor scalars ids bounds priorFamily afterFamily fits outside complement outside)
    (MdocOracleWindows.merkle_domain binary prime cantor scalars bounds priorFamily afterFamily)
    (MdocOracleWindows.transcript_covers binary prime cantor scalars ids bounds priorFamily afterFamily fits outside)
  -- Erase only the support-membership proof. Both original raw traces and
  -- the observer's private context remain in the distinguishing view.
  have mapped := statClose_map (ObserverStateful.mapContext (QM := Bytes) (AM := Digest) (QT := Bytes) (AT := Digest × Answer)
    (Proof := Option (MdocOracleWindows.Output binary prime bounds)) (Out := Observed) (Context := Supported) Subtype.val) finiteLaw
  have realErase := erase_honest_support binary prime cantor scalars ids bounds original remaining requestOf outside fits priorFamily afterFamily
  have simErase := erase_simulated_support binary prime cantor scalars ids bounds requestOf outside fits priorFamily afterFamily
  simpa only [Function.comp_apply,realErase,simErase] using
    (Probability.changeFintype mapped)

end Family

omit [Fintype B] [DecidableEq B] in
/-- Every non-Merkle runtime factory reads the same complementary SHA
slice, so the raw theorem's endpoints are the actual factories evaluated
at the complete sampled SHA oracle. -/
theorem setup_extend (large : Finset Bytes) (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)
    (table : {raw // raw ∈ large} → Digest) :
    (Setup (OracleWindow.extend large table outside)) = (Setup outside) := by
  have same := MdocPublicSetup.setup_merge binary prime cantor scalars ids bounds outside (OracleWindow.extend large table outside)
  have merged : SHAOracle.merge SHAOracle.merkleDomain outside (OracleWindow.extend large table outside) = OracleWindow.extend large table outside :=
    BackendRuntimeContextGlobal.merge_oracle outside large onlyMerkle table
  rw [merged] at same
  exact same

omit [Fintype B] [DecidableEq B] in
theorem metadata_extend (large : Finset Bytes) (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)
    (table : {raw // raw ∈ large} → Digest) :
    (Meta (OracleWindow.extend large table outside)) = (Meta outside) := by
  have same := MdocPublicSetup.metadata_merge binary prime cantor scalars ids bounds outside (OracleWindow.extend large table outside)
  have merged : SHAOracle.merge SHAOracle.merkleDomain outside (OracleWindow.extend large table outside) = OracleWindow.extend large table outside :=
    BackendRuntimeContextGlobal.merge_oracle outside large onlyMerkle table
  rw [merged] at same
  exact same

end LfzkV2.Current.ZeroKnowledge.MdocContextPrivacy
