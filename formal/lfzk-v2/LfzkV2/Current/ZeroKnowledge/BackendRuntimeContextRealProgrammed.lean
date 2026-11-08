import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRealView
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRefreshProgrammed

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeContext BackendRuntimeContextEncoding
open BackendRuntimeReal (refreshedForRequest)
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run

variable {B C Observed : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [DecidableEq Observed]
variable {Context : Type} [Fintype Context]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Trace" => List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × C))
local notation "Prefix" => Context × Trace

variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)

variable {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  Context preM preT)
variable (after : Context →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

variable (outside : Bytes → Digest)

attribute [local instance] BackendRuntime.requestFintype BackendRuntime.leafFintype
  BackendRuntime.frontCoinsFintype BackendRuntime.genericBackendMasksFintype
  BackendRuntime.backendMasksFintype BackendRuntime.merkleCoinsFintype BackendRuntime.coinsFintype

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem real_observed_refreshed (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (labels : Fin (2*2443-1) → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (sample : Fin 361 → B)
    :
    let fullHM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
    let earlier := Observer.run fullHM H prior
    let request := requestOf earlier.1
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let configuration := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
      (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside draw original remaining H answer
        (privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside
          (OracleHonestCoins.assemble binary prime binaryNodes frame sample) HM labels) =
      observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2 fullHM H
        (refreshedForRequest b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata draw
          (original request) (remaining request) source sample request fullHM H answer) := by
  let tape := OracleHonestCoins.assemble binary prime binaryNodes frame sample
  let coin := privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside tape HM labels
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let fullHM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
  have observed := real_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside original remaining draw H answer coin
  have completed := realCompletion_assembled binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside original remaining draw H answer frame sample HM labels
  have finished := congrArg (observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2 fullHM H) completed
  let post := fun priorState : Prefix =>
    let request := requestOf priorState.1
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let configuration := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
      (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    observeCompletion binary prime primePlan repr shape setup after priorState.1 priorState.2 fullHM H
      (refreshedForRequest b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata draw
        (original request) (remaining request) source sample request fullHM H answer)
  have priorView := SHAObserverWindow.before_output SHAOracle.merkleDomain outside
    (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
    (codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg) HM H
  have result := observed.trans (finished.trans (congrArg post priorView))
  exact result

omit [DecidableEq Observed] in
theorem real_eq_programmed (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (labels : Fin (2*2443-1) → Digest) (H : Point → Digest × C) (answer : Digest × C) (sample : Fin 361 → B)
    (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
      (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM)
      (requestOf (Observer.run (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H prior).1) H sample) :
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside draw original remaining H answer
      (privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside
        (OracleHonestCoins.assemble binary prime binaryNodes frame sample) HM labels) =
      programmedView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside original remaining draw frame HM (sample,(H,answer)) := by
  let fullHM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
  let earlier := ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1
  let post := fun priorState : Prefix =>
    let request := requestOf priorState.1
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let configuration := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
      (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    observeCompletion binary prime primePlan repr shape setup after priorState.1 priorState.2 fullHM H
      (refreshedForRequest b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata draw
        (original request) (remaining request) source sample request fullHM H answer)
  have priorEq : earlier = Observer.run fullHM H prior :=
    congrArg Prod.fst (Observer.fixMerkle_run H fullHM prior)
  have requestEq := congrArg (fun priorState : Prefix => requestOf priorState.1) priorEq
  have valid : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0) fullHM
      (requestOf earlier.1) H sample := by
    rw [requestEq]
    exact hash
  have source := refreshed_observation_stored binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside original remaining draw frame HM H answer sample pivotOne valid
  have moved := congrArg post priorEq
  have actual := real_observed_refreshed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside original remaining draw frame HM labels H answer sample
  exact actual.trans (moved.symm.trans source)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
