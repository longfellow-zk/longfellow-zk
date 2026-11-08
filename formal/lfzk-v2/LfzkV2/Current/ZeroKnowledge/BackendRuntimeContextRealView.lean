import LfzkV2.Current.ZeroKnowledge.RequestedBackend
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRealCoins

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeContext BackendRuntimeContextEncoding
open BackendRuntimeReal (complete_pending refreshedForRequest)
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
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)

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

def realCompletion (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := realLabels binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin
  let frontend := BackendRuntimeContext.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf original remaining H coin.1.1 earlier labels
  let cells := BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coin.1.1 earlier
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    cells coin.1.2
  let responses := MerkleBackend.realResponses (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (OrderedOpening.query (cfg.sample answer.2)) cells
    (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf original remaining H coin.1.1 earlier labels)
    (BackendRuntimeContext.batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf draw original remaining H coin.1.1 earlier labels) coin.1.2
  CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata (requestOf earlier.1) (cfg.sample answer.2) frontend responses (fun i => columns i.val)
    (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
      (cfg.sample answer.2) coin.2.2.1 columns) H answer

omit [DecidableEq Observed] in
theorem real_output (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside draw original remaining H answer coin =
      observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2
        (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) H
        (realCompletion binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
          requestOf prior after outside original remaining draw H answer coin) := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let labels := realLabels binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin
  let frontend := BackendRuntimeContext.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf original remaining H coin.1.1 earlier labels
  let cells := BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coin.1.1 earlier
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    cells coin.1.2
  let responses := MerkleBackend.realResponses (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (OrderedOpening.query (cfg.sample answer.2)) cells
    (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf original remaining H coin.1.1 earlier labels)
    (BackendRuntimeContext.batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf draw original remaining H coin.1.1 earlier labels) coin.1.2
  exact runView_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside coin.2.1 H answer earlier (frontend,responses) columns coin.2.2.1 labels

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem realCompletion_assembled (H : Point → Digest × C) (answer : Digest × C)
    (frame : OracleHonestCoins.Frame binary prime binaryNodes) (sample : Fin 361 → B)
    (HM : {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (labels : Fin (2*2443-1) → Digest) :
    let tape := OracleHonestCoins.assemble binary prime binaryNodes frame sample
    let coin := privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside tape HM labels
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let request := requestOf earlier.1
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
      (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    realCompletion binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside original remaining draw H answer coin =
      refreshedForRequest b p primePlan binaryNodes repr shape setup config binaryCount primeCount metadata draw
        (original request) (remaining request) source sample request
        (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H answer := by
  let tape := OracleHonestCoins.assemble binary prime binaryNodes frame sample
  let coin := privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside tape HM labels
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let request := requestOf earlier.1
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
    (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
  let fullHM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
  let actualLabels := realLabels binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin
  let frontend := BackendRuntimeContext.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf original remaining H coin.1.1 earlier actualLabels
  let logical := HonestRuntime.logical binary prime binaryNodes (original request) (remaining request) tape
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    logical tape.backend
  let response : Body → JointResponse.Response (First).participant (Second).participant := fun body =>
    CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public logical
      (((CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount primeCount metadata request body H).map (fun data => data.2.statement)).getD
          (BackendRuntime.zeroStatement binary prime primePlan binaryNodes repr shape setup cfg))
      (CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata draw request body H) tape.backend
  let complete : Body → Option (Output × (Point → Digest × C)) := fun body =>
    CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata request (cfg.sample answer.2) body (response body) (fun i => columns i.val)
      (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        fullHM (cfg.sample answer.2) tape.nonces columns) H answer
  have originalEq : realCompletion binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside original remaining draw H answer coin = complete frontend := by rfl
  have frontendEq : frontend =
      (OracleHonestRuntime.frontend b p primePlan binaryNodes repr shape setup config binaryCount metadata
        (original request) (remaining request) source request fullHM H sample).body :=
    front_result binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside original remaining H coin
  have changed := congrArg complete frontendEq
  have core := complete_pending b p primePlan binaryNodes repr shape setup config binaryCount primeCount metadata draw
    (original request) (remaining request) source sample request fullHM H answer
  let privateTape := OracleHonestRuntime.tapeAt b p binaryNodes source sample
  have logicalEq : HonestRuntime.logical b p binaryNodes (original request) (remaining request) source = logical := rfl
  have backendEq : privateTape.backend = tape.backend := rfl
  have noncesEq : privateTape.nonces = tape.nonces := rfl
  dsimp only at core
  erw [logicalEq,backendEq,noncesEq] at core
  dsimp only [OracleHonestRuntime.statement,OracleHonestRuntime.statementAt,OracleHonestRuntime.zeroStatement] at core
  erw [RequestedBackend.statement binary prime primePlan binaryNodes repr shape setup cfg
    binaryCount primeCount metadata request] at core
  erw [RequestedBackend.batching binary prime primePlan binaryNodes repr shape setup cfg
    binaryCount primeCount metadata draw request] at core
  erw [RequestedBackend.responses binary prime primePlan binaryNodes repr shape setup cfg primeCount request] at core
  erw [RequestedBackend.complete binary prime primePlan binaryNodes repr shape setup cfg
    binaryCount primeCount metadata request] at core
  exact originalEq.trans (changed.trans core)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
