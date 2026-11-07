import LfzkV2.Current.ZeroKnowledge.BackendRuntime
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Stateful observer routing and backend simulation. Private observer
context is retained through both phases, while protocol callbacks receive
only its selected canonical request. The finite context type is supplied
by the original raw observer support construction. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate
attribute [local irreducible] BackendRuntime.hashChecks
attribute [local irreducible] StatClose probOf

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
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)
local notation "Trace" => List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × C))
local notation "Prefix" => Context × Trace
local notation "FrontCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BGeo" => Backend.profileGeometry binaryNodes
local notation "NGeo" => Backend.profileGeometry ConcreteSetup.primeNodes

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

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)

def trees := SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after

def window := BackendRuntime.windowContextForTrees binary prime primePlan binaryNodes repr shape setup cfg
  (trees binary prime primePlan repr shape setup prior after outside)

def finiteCodec := BackendRuntime.finiteCodecContextForTrees binary prime primePlan binaryNodes repr shape setup cfg
  (trees binary prime primePlan repr shape setup prior after outside)

def expanded (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) : Bytes → Digest :=
  OracleWindow.extend (window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) HM outside

def project (earlier : Prefix) : Request × Trace :=
  BackendRuntime.publicPrefix binary prime primePlan repr shape setup requestOf earlier

def cells (coins : FrontCoins) (earlier : Prefix) :=
  BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coins
    (project binary prime primePlan repr shape setup requestOf earlier)

variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)

def front (coins : FrontCoins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def statements (coins : FrontCoins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def batching (coins : FrontCoins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H draw coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def frontSimulation (coins : CompleteSimulation.Coins binary prime) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def publicStatements (coins : CompleteSimulation.Coins binary prime) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def publicBatching (coins : CompleteSimulation.Coins binary prime) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  BackendRuntime.publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H draw coins
    (project binary prime primePlan repr shape setup requestOf earlier) labels

def before := BackendRuntime.beforeContextForTrees binary prime primePlan binaryNodes repr shape setup cfg
  (trees binary prime primePlan repr shape setup prior after outside) H

variable (answer : Digest × C)

def observer := BackendRuntime.observerContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  H answer requestOf (trees binary prime primePlan repr shape setup prior after outside)

def real := BackendRuntime.realContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  original remaining H draw answer requestOf (trees binary prime primePlan repr shape setup prior after outside)

def simulatedBackend := BackendRuntime.simulatedBackendContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  original remaining H draw answer requestOf (trees binary prime primePlan repr shape setup prior after outside)

def simulatedPublic := BackendRuntime.simulatedPublicContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  H draw answer requestOf (trees binary prime primePlan repr shape setup prior after outside)

abbrev Shared := CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads) ×
    MerklePreparation.Coins (Salt := Digest) (Digest := Digest)
      (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside}) 2443

abbrev PrivateCoins := BackendCompiled.Coins (FrontCoin := CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
  (Nonce := Digest) (D := Digest)
  (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside})
  (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
  (bw := rows binary.description.cells) (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)

abbrev PublicCoins := BackendCompiled.Coins (FrontCoin := CompleteSimulation.Coins binary prime)
  (Nonce := Digest) (D := Digest)
  (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside})
  (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
  (bw := rows binary.description.cells) (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)

def priorStateOf (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) : Prefix :=
  ((before binary prime primePlan binaryNodes repr shape setup cfg prior after outside H).run shared.2.1).1

def dummyLabels (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) : Fin (2*2443-1) → Digest :=
  MerklePreparation.honestLabels (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)) 2443
    (before binary prime primePlan binaryNodes repr shape setup cfg prior after outside H)
    (BackendCompiled.simMessages (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) id shared.1)
    shared.2.2.1 shared.2.1

/-- Public statements are required to have witnesses only when an actual
same-SHA prior execution can select them. The observer's complete private
state and trace remain available for all later queries. -/
def RequestReachable (request : Request) : Prop :=
  ∃ (inside : Bytes → Digest) (HT : Point → Digest × C),
    requestOf (Observer.run (SHAOracle.merge SHAOracle.merkleDomain outside inside) HT prior).1 = request

omit [DecidableEq Observed] in
theorem before_reachable
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) :
    RequestReachable binary prime primePlan repr shape setup requestOf prior outside
      (requestOf (((before binary prime primePlan binaryNodes repr shape setup cfg prior after outside H).run HM).1.1)) := by
  have output := SHAObserverWindow.before_output SHAOracle.merkleDomain outside
    (BackendRuntime.codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (BackendRuntime.codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
    (BackendRuntime.codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg) HM H
  refine ⟨expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM,H,?_⟩
  have merged : SHAOracle.merge SHAOracle.merkleDomain outside
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) =
      expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM :=
    SHAObserverWindow.merge_extend SHAOracle.merkleDomain outside
      (BackendRuntime.codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
      (BackendRuntime.codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
      (BackendRuntime.codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg) HM
  rw [merged]
  exact (congrArg (fun earlierState => requestOf earlierState.1) output).symm

omit [DecidableEq Observed] in
theorem priorStateOf_reachable (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    RequestReachable binary prime primePlan repr shape setup requestOf prior outside
      (requestOf (priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H shared).1) :=
  before_reachable binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside H shared.2.1

omit [DecidableEq Observed] in
theorem backend_hiding
    (satisfied : ∀ (coins : FrontCoins) (earlier : Prefix) labels,
      RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).1.Satisfies
        (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).1) ∧
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).2.Satisfies
        (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining H answer)
      (simulatedBackend binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining H answer) := by
  have codecInj := SHAObserverWindow.finiteCodec_inj SHAOracle.merkleDomain outside
    (BackendRuntime.codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (MerkleRuntime.codec_inj (First).participant (Second).participant repr cfg.binaryField cfg.primeField setup.jointContext (by decide))
  have compiled := BackendCompiled.simulator_statClose_on_runs (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    (before binary prime primePlan binaryNodes repr shape setup cfg prior after outside H)
    postM (OrderedOpening.query (cfg.sample answer.2)) 0 id
    (cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining)
    (front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H)
    (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H)
    (batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf draw original remaining H)
    (observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer)
    (by decide) codecInj (fun coins HM labels => satisfied coins _ labels
      (before_reachable binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside H HM))
  simp only [QuerySet.card_coordinates] at compiled
  convert compiled using 1 <;> rfl

variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀
    (earlier : Context × List (Observer.Event (QM := Bytes) (AM := Digest)
      (QT := QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (AT := Digest × C))) labels,
  RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
  BackendRuntime.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H
    (BackendRuntime.publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)

def fiber (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    FrontCoins ≃ CompleteSimulation.Coins binary prime :=
  let earlier := priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H shared
  let labels := dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H shared
  BackendRuntime.frontendEquivAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
    pivotOne (project binary prime primePlan repr shape setup requestOf earlier) labels
    (validHash earlier labels (priorStateOf_reachable binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside H shared))

private def frontendOrder {FrontendSpace MaskSpace MerkleSpace : Type} :
    ((FrontendSpace × MaskSpace) × MerkleSpace) ≃ ((MaskSpace × MerkleSpace) × FrontendSpace) where
  toFun coin := ((coin.1.2,coin.2),coin.1.1)
  invFun coin := ((coin.2,coin.1.1),coin.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def frontendCoupling : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside :=
  (frontendOrder.trans (Equiv.prodCongrRight fun shared =>
    fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      original remaining H pivotOne validHash shared)).trans frontendOrder.symm

omit [DecidableEq Observed] in
theorem frontendCoupling_apply (coin : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
        original remaining H pivotOne validHash coin =
      ((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
        original remaining H pivotOne validHash (coin.1.2,coin.2) coin.1.1,coin.1.2),coin.2) := rfl

omit [DecidableEq Observed] in
theorem frontendCoupling_view (coin : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw H answer
        (frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
          original remaining H pivotOne validHash coin) =
      simulatedBackend binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining H answer coin := by
  rcases coin with ⟨⟨frontend,backend⟩,merkle⟩
  let earlier := priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle)
  let labels := dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle)
  let selected := project binary prime primePlan repr shape setup requestOf earlier
  have view := BackendRuntime.front_equiv_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H pivotOne selected labels
    (validHash earlier labels (priorStateOf_reachable binary prime primePlan binaryNodes repr shape setup cfg requestOf prior after outside H (backend,merkle))) frontend
  let post := fun body : Body => BackendCompiled.runView
    (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    postM (OrderedOpening.query (cfg.sample answer.2)) id
    (observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside H answer)
    earlier (MerkleBackend.simColumns BGeo NGeo backend)
    (body,MerkleBackend.simResponses BGeo NGeo (OrderedOpening.query (cfg.sample answer.2)) (0 : Fin 265)
      (((CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg binaryCount primeCount metadata
        (requestOf earlier.1) body H).map (fun data => data.2.statement)).getD
          (BackendRuntime.zeroStatement binary prime primePlan binaryNodes repr shape setup cfg))
      (CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg binaryCount metadata draw
        (requestOf earlier.1) body H) backend)
    merkle.2.1 merkle.1 labels
  rw [frontendCoupling_apply]
  convert congrArg post view using 1 <;> rfl

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem simulator_statClose
    (satisfied : ∀ (coins : FrontCoins) (earlier : Prefix) labels,
      RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).1.Satisfies
        (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).1) ∧
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).2.Satisfies
        (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining H answer)
      (simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw H answer) := by
  have backend := backend_hiding binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
    draw original remaining H answer satisfied
  have frontend := statClose_zero_of_equiv
    (frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      original remaining H pivotOne validHash)
    (fun coin => (frontendCoupling_view binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      draw original remaining H answer pivotOne validHash coin).symm)
  have combined := backend.trans frontend
  simp only [add_zero] at combined
  exact Probability.changeFintype combined

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext
