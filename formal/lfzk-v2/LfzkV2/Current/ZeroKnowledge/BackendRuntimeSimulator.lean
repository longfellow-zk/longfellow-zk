import LfzkV2.Current.ZeroKnowledge.BackendRuntimeEncoding

/-! Identify the public endpoint of the backend/frontend coin changes with
the complete witness-free simulator. The commitment is already the zero-cell
commitment here, so its root stays fixed while the frontend coins change.
The final identities preserve the proof and both observer traces together. -/

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeSimulator
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate

variable {B C Observed : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [DecidableEq Observed]
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
local notation "Prefix" => Request × Trace

variable {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
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
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    (BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels).commitment =
      CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
        (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) := by
  exact dummy_root binary prime primePlan binaryNodes repr shape setup cfg prior after outside H answer coin

omit [DecidableEq Observed] in
theorem front_committed (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
    CompleteCanonicalVerifier.committedFrontend binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) coin.2.2.1 coin.1.2 frontend = frontend := by
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
  have fixed (body : Body) (value : Digest) (same : body.commitment = value) : {body with commitment := value} = body := by
    cases body
    cases same
    rfl
  apply fixed frontend
  exact frontend_commitment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer coin

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem front_result (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let request := earlier.1
    let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels =
      CompleteFrontendBody.body b p primePlan (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM
        (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape))
        (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata request HM H
          (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape)) := by
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let request := earlier.1
  let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
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
  let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
  have roots := frontend_commitment binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer coin
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

omit [DecidableEq Observed] [Fintype C] in
theorem complete_requested (request : Request) (HM : Bytes → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → Digest)
    (backend : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) (frontend : Body) :
    CompleteCanonicalVerifier.complete
      (RequestedSimulator.requestedBinary binary prime primePlan shape request).description
      (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request)
      binaryNodes ConcreteSetup.primeNodes repr shape setup
      (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
      binaryCount primeCount metadata draw request HM indices nonces backend frontend H answer =
      CompleteCanonicalVerifier.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount primeCount metadata draw request HM indices nonces backend frontend H answer := by
  rfl

omit [DecidableEq Observed] in
theorem completed (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
    let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata earlier.1 (cfg.sample answer.2) frontend
      (CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query (cfg.sample answer.2))
        (BackendRuntime.publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels)
        (BackendRuntime.publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H draw coin.1.1 earlier labels) coin.1.2)
      (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2 i.val)
      (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg HM
        (cfg.sample answer.2) coin.2.2.1
        (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2)) H answer =
      RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        earlier.1 HM H (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) := by
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
  let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
  let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape earlier.1
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount earlier.1
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount earlier.1
  let requestedTape := RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount earlier.1 tape
  let actualBody := CompleteFrontendBody.body b p primePlan
    (CompleteSimulator.commitment b p primePlan binaryNodes repr shape setup config HM requestedTape)
    (CompleteSimulator.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata earlier.1 HM H requestedTape)
  let indices := cfg.sample answer.2
  let opening := CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg HM
    indices coin.2.2.1 (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2)
  let columns := fun i : ↥(OrderedOpening.query indices).coordinates =>
    MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2 i.val
  let response := fun body : Body => CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query indices)
    (CompleteObserverSimulation.statement binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata earlier.1 body H)
    (CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata draw earlier.1 body H) coin.1.2
  let finish := fun resp => CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata earlier.1 indices frontend resp columns opening H answer
  have fixed := front_committed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer coin
  have responseEq := congrArg response fixed
  have publicEq := congrArg finish responseEq
  have encoded := CompleteObserverSimulation.complete_dummy binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata draw earlier.1 HM indices coin.2.2.1 coin.1.2 frontend H answer
  have original := publicEq.symm.trans encoded
  let complete := fun body : Body => CompleteCanonicalVerifier.complete binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata draw earlier.1 HM indices coin.2.2.1 coin.1.2 body H answer
  have body := front_result binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer coin
  have bodyCompleted := congrArg complete body
  have requested := complete_requested binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    earlier.1 HM H answer indices coin.2.2.1 coin.1.2 actualBody
  have result := original.trans (bodyCompleted.trans requested.symm)
  convert result using 1 <;> rfl

omit [DecidableEq Observed] [Fintype C] in
theorem experiment_eq_observe (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :
    RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw prior after tape HM H =
      CompleteSimulator.observeCompletion binary prime primePlan repr shape setup after
        (Observer.run HM H prior).1 (Observer.run HM H prior).2 HM H
        (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          (Observer.run HM H prior).1 HM H tape) := by
  unfold RequestedExperiment.simulated Observer.experiment RequestedExperiment.simulatedForRequest CompleteSimulator.observeCompletion
  dsimp only
  cases RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    (Observer.run HM H prior).1 HM H tape <;> rfl

omit [DecidableEq Observed] in
theorem simulatedPublic_eq (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    BackendRuntime.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      prior after outside H draw answer coin =
      RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        prior after (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin)
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) H := by
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let frontend := BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
  let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
  let tape := simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin
  let statement := BackendRuntime.publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coin.1.1 earlier labels
  let batch := BackendRuntime.publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H draw coin.1.1 earlier labels
  let response := CompleteBackend.responses binaryNodes ConcreteSetup.primeNodes binary.description.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query (cfg.sample answer.2)) statement batch coin.1.2
  have openingView := runView_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside coin.2.1 H answer earlier (frontend,response)
    (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2) coin.2.2.1 labels
  have publicCompletion := completed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside draw H answer coin
  have finished := congrArg (CompleteSimulator.observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2 HM H) publicCompletion
  let post := fun priorState : Prefix => CompleteSimulator.observeCompletion binary prime primePlan repr shape setup after
    priorState.1 priorState.2 HM H
    (RequestedSimulator.forRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      priorState.1 HM H tape)
  have priorView := SHAObserverWindow.before_output SHAOracle.merkleDomain outside
    (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
    (codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg) coin.2.1 H
  have result := openingView.trans (finished.trans (congrArg post priorView))
  have final := experiment_eq_observe binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after draw tape HM H
  have exactResult := result.trans final.symm
  convert exactResult using 1
  rfl

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀ earlier labels,
  BackendRuntime.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original H earlier labels)

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem simulator_statClose (answer : Digest × C)
    (satisfied : ∀ coins earlier labels,
      (BackendRuntime.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins earlier labels).1.Satisfies (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coins earlier).1) ∧
      (BackendRuntime.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins earlier labels).2.Satisfies (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (BackendRuntime.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining H draw answer)
      (fun coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside =>
        RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
          prior after (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin)
          (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) H) := by
  have bound := BackendRuntime.simulator_statClose binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside original remaining H draw answer pivotOne validHash satisfied
  have view := funext (simulatedPublic_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside draw H answer)
  rw [view] at bound
  convert bound using 1
  rfl

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeSimulator
