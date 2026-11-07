import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextEncoding
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeSimulator
import LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment

/-! Identify the public endpoint of the backend/frontend coin changes with
the complete witness-free simulator. The commitment is already the zero-cell
commitment here, so its root stays fixed while the frontend coins change.
The final identities preserve the proof and both observer traces together. -/

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextSimulator
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeContext BackendRuntimeContextEncoding
open BackendRuntimeSimulator (complete_requested)
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate

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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)
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

omit [DecidableEq Observed] in
/-- Read the stored commitment directly. Keeping this scalar boundary avoids
comparing whole frontend executions merely to identify their common root. -/
theorem frontend_commitment (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    (BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels).commitment =
      CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg
        (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
        (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) := by
  exact dummy_root binary prime primePlan binaryNodes repr shape setup cfg prior after outside H answer coin

omit [DecidableEq Observed] in
theorem front_committed (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
    CompleteCanonicalVerifier.committedFrontend binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) coin.2.2.1 coin.1.2 frontend = frontend := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
  have fixed (body : Body) (value : Digest) (same : body.commitment = value) : {body with commitment := value} = body := by
    cases body
    cases same
    rfl
  apply fixed frontend
  exact frontend_commitment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer coin

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem front_result (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let request := requestOf earlier.1
    let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels =
      CompleteFrontendBody.body b p primePlan (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM
        (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape))
        (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata request HM H
          (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape)) := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let request := requestOf earlier.1
  let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
  let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let encode : Digest → Body := fun root => CompleteFrontendBody.body b p primePlan root
    (CompleteSimulation.simulate b p primePlan
      (CompleteSimulator.samples b p primePlan binaryNodes repr shape setup config)
      (CompleteSimulator.base b p primePlan binaryNodes repr shape setup config binaryCount metadata request root) H
      (FingerprintPrefix.context request root)
      (RequestedSimulator.publicFrontendEquiv binary prime primePlan shape primeCount request coin.1.1))
  let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
  have roots := frontend_commitment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer coin
  have requestRoot := requested_commitment binary prime primePlan binaryNodes repr shape setup cfg primeCount request HM tape
  have self : encode frontend.commitment = frontend := by rfl
  have equal := congrArg encode (roots.trans requestRoot.symm)
  have actual : encode (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM
      (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape)) =
      CompleteFrontendBody.body b p primePlan (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM
        (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape))
        (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata request HM H
          (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape)) := by rfl
  exact self.symm.trans (equal.trans actual)

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

omit [DecidableEq Observed] in
theorem completed (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
    let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata (requestOf earlier.1) (cfg.sample answer.2) frontend
      (CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query (cfg.sample answer.2))
        (BackendRuntimeContext.publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels)
        (BackendRuntimeContext.publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf draw H coin.1.1 earlier labels) coin.1.2)
      (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2 i.val)
      (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg HM
        (cfg.sample answer.2) coin.2.2.1
        (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2)) H answer =
      RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        (requestOf earlier.1) HM H (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
  let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
  let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape (requestOf earlier.1)
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount (requestOf earlier.1)
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount (requestOf earlier.1)
  let requestedTape := RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount (requestOf earlier.1) tape
  let actualBody := CompleteFrontendBody.body b p primePlan
    (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM requestedTape)
    (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata (requestOf earlier.1) HM H requestedTape)
  let indices := cfg.sample answer.2
  let opening := CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg HM
    indices coin.2.2.1 (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2)
  let columns := fun i : ↥(OrderedOpening.query indices).coordinates =>
    MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2 i.val
  let response := fun body : Body => CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query indices)
    (CompleteObserverSimulation.statement binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata (requestOf earlier.1) body H)
    (CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata draw (requestOf earlier.1) body H) coin.1.2
  let finish := fun resp => CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata (requestOf earlier.1) indices frontend resp columns opening H answer
  have fixed := front_committed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer coin
  have responseEq := congrArg response fixed
  have publicEq := congrArg finish responseEq
  have encoded := CompleteObserverSimulation.complete_dummy binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata draw (requestOf earlier.1) HM indices coin.2.2.1 coin.1.2 frontend H answer
  have original := publicEq.symm.trans encoded
  let complete := fun body : Body => CompleteCanonicalVerifier.complete binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata draw (requestOf earlier.1) HM indices coin.2.2.1 coin.1.2 body H answer
  have body := front_result binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer coin
  have bodyCompleted := congrArg complete body
  have requested := complete_requested binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (requestOf earlier.1) HM H answer indices coin.2.2.1 coin.1.2 actualBody
  have result := original.trans (bodyCompleted.trans requested.symm)
  convert result using 1 <;> rfl

omit [DecidableEq Observed] [Fintype C] [Fintype Context] in
theorem experiment_eq_observe (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :
    RequestedContextExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw requestOf prior after tape HM H =
      observeCompletion binary prime primePlan repr shape setup after
        (Observer.run HM H prior).1 (Observer.run HM H prior).2 HM H
        (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          (requestOf (Observer.run HM H prior).1) HM H tape) := by
  unfold RequestedContextExperiment.simulated ObserverStateful.experiment ObserverStateful.callback Observer.experiment RequestedExperiment.simulatedForRequest observeCompletion
  dsimp only
  cases RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (requestOf (Observer.run HM H prior).1) HM H tape <;> rfl

omit [DecidableEq Observed] in
theorem simulatedPublic_eq (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside draw H answer coin =
      RequestedContextExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        requestOf prior after (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin)
        (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) H := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntimeContext.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntimeContext.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
  let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
  let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
  let statement := BackendRuntimeContext.publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf H coin.1.1 earlier labels
  let batch := BackendRuntimeContext.publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf draw H coin.1.1 earlier labels
  let response := CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query (cfg.sample answer.2)) statement batch coin.1.2
  have openingView := runView_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside coin.2.1 H answer earlier (frontend,response)
    (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2) coin.2.2.1 labels
  have publicCompletion := completed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside draw H answer coin
  have finished := congrArg (observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2 HM H) publicCompletion
  let post := fun priorState : Prefix => observeCompletion binary prime primePlan repr shape setup after
    priorState.1 priorState.2 HM H
    (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      (requestOf priorState.1) HM H tape)
  have priorView := SHAObserverWindow.before_output SHAOracle.merkleDomain outside
    (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
    (codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg) coin.2.1 H
  have result := openingView.trans (finished.trans (congrArg post priorView))
  have final := experiment_eq_observe binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after draw tape HM H
  have exactResult := result.trans final.symm
  convert exactResult using 1
  rfl


end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextSimulator
