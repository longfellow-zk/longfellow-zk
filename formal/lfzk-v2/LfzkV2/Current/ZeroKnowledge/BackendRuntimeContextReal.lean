import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextEncoding
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshGames
import LfzkV2.Current.ZeroKnowledge.CompleteTerminalOpening

/-! Identify the real backend view with the actual complete honest proof
when its single opening answer is independently refreshed. The original
source tape, authentication and final seal are retained. -/

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeContext BackendRuntimeContextEncoding
open BackendRuntimeReal (real_columns requested_commitment)
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

def honestTape
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    HonestRuntime.Tape binary prime binaryNodes :=
  ⟨coin.1.1.1,coin.1.1.2,coin.1.2,coin.2.2.1⟩

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)

def realLabels (original : Request → Fin binary.nPrivate → Bool)
    (remaining : Request → Fin prime.remaining → N) (H : Point → Digest × C)
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  MerklePreparation.honestLabels
    (MerkleSimulation.nonceCodec (BackendRuntimeContext.finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)) 2443
    (BackendRuntimeContext.before binary prime primePlan binaryNodes repr shape setup cfg prior after outside H)
    (BackendCompiled.realMessages (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) id
      (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining) coin.1.1 coin.1.2)
    coin.2.2.1 coin.2.1

omit [DecidableEq Observed] in
theorem root_eq (H : Point → Digest × C)
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    realLabels binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin ⟨2*2443-2,by decide⟩ =
      HonestRuntime.commitment binary prime primePlan binaryNodes repr shape setup cfg (original (requestOf earlier.1)) (remaining (requestOf earlier.1))
        (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
        (honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin) := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coin.1.1 earlier) coin.1.2
  have value := committed_root binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1 coin.2.2.1 columns
  have equal := real_columns binary prime primePlan binaryNodes repr shape setup cfg (original (requestOf earlier.1)) (remaining (requestOf earlier.1)) tape
  have rooted := congrArg (fun columns => root
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle
      (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1))
      2443 (fun i => (i,coin.2.2.1 i)) columns) equal
  exact value.trans rooted

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem front_result (H : Point → Digest × C)
    (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := realLabels binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin
    let request := requestOf earlier.1
    let HM := BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape
    BackendRuntimeContext.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H
      coin.1.1 earlier labels =
      CompleteFrontendBody.rawBody b p primePlan
        (HonestRuntime.commitment b p primePlan binaryNodes repr shape setup config (original request) (remaining request) HM source)
        (HonestRuntime.frontendResult b p primePlan binaryNodes repr shape setup config binaryCount metadata
          (original request) (remaining request) request HM H source) := by
  let earlier := BackendRuntimeContext.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let request := requestOf earlier.1
  let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape
  let encode : Digest → Body := fun root => CompleteFrontendBody.rawBody b p primePlan root
    (HonestRuntime.frontendAtRoot b p primePlan binaryNodes repr shape setup config binaryCount metadata
      (original request) (remaining request) request root H source.frontend source.selectors)
  have roots := root_eq binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside original remaining H coin
  have requested := requested_commitment binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    (original request) (remaining request) tape
    (BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
  have equal := congrArg encode (roots.trans requested.symm)
  exact equal


end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
