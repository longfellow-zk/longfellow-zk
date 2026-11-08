import LfzkV2.Current.ZeroKnowledge.RequestedExperiment
import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling
import LfzkV2.Current.ZeroKnowledge.BackendCompiled
import LfzkV2.Current.ZeroKnowledge.CompleteObserver
import LfzkV2.Current.ZeroKnowledge.SHAObserverWindow

/-! The concrete fixed-opening-answer backend hybrid. The frontend is the
actual honest current frontend at the shared root, with the prior observer's
chosen public values installed. Statements and batching coins are read by the
actual canonical runtime. The observer encodes the full proof solely from
the public backend view and uses the resulting programmed transcript oracle.

The finite Merkle window is fixed across all requests and complete proofs.
Ordinary affine satisfaction is the remaining algebraic interface, discharged
by the honest frontend/compiler theorem when this hybrid is composed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntime
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

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
local notation "Trace" => List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × C))
local notation "Prefix" => Request × Trace
local notation "FrontCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)
local notation "BGeo" => Backend.profileGeometry binaryNodes
local notation "NGeo" => Backend.profileGeometry ConcreteSetup.primeNodes

variable {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

variable (outside : Bytes → Digest)

local instance requestFintype : Fintype (CanonicalRequest.Request shape binary.description.nPublic) := by
  apply Fintype.ofInjective (fun request : CanonicalRequest.Request shape binary.description.nPublic =>
    (request.session,request.publicBits,request.primeInputs))
  intro a b same
  cases a
  cases b
  cases same
  rfl

local instance leafFintype : Fintype
    (MerkleCompiler.Leaf (First).participant.Carrier (First).participant.backend.nw 0 ×
      MerkleCompiler.Leaf (Second).participant.Carrier (Second).participant.backend.nw 0) := by
  change Fintype (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
    MerkleCompiler.Leaf N (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0)
  letI : Fintype (MerkleCompiler.Leaf B (rows binary.description.cells) 0) :=
    Fintype.ofEquiv _ (OpeningBody.leafEquiv B (rows binary.description.cells))
  letI : Fintype (MerkleCompiler.Leaf N (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0) :=
    Fintype.ofEquiv _ (OpeningBody.leafEquiv N (rows (CellLayout.Prime.cells prime.remaining prime.pads)))
  infer_instance

def codec := MerkleRuntime.codec (First).participant (Second).participant repr
  cfg.binaryField cfg.primeField setup.jointContext (by decide)

omit [Fintype C] in
theorem codec_leaf_domain (value) :
    SHAOracle.merkleDomain ((codec binary prime primePlan binaryNodes repr shape setup cfg).leafEnc value) :=
  SHAOracle.leaf_in_domain (First).participant (Second).participant repr cfg.binaryField cfg.primeField
    setup.jointContext (by decide) (value.1,MerkleRuntime.tupleLeaf (First).participant (Second).participant value.2)

omit [Fintype C] in
theorem codec_node_domain (value) :
    SHAOracle.merkleDomain ((codec binary prime primePlan binaryNodes repr shape setup cfg).nodeEnc value) :=
  SHAOracle.node_in_domain (First).participant (Second).participant repr cfg.binaryField cfg.primeField
    setup.jointContext (by decide) value

/-- The residual observer is the only place where the complementary SHA
answers enter the finite backend experiment. Keeping it as data makes that
dependence explicit without expanding a protocol execution. -/
abbrev ContextTreeFamily (Context : Type) :=
  (index : ObserverWindow.Index Context (Option Output)) →
    Merkle.RandomOracle.TwoOracleTree Bytes Digest Point (Digest × C)
      (SHAObserverWindow.Results (Raw := Bytes) (D := Digest) (QT := Point) (AT := Digest × C)
        (Observed := Observed) index)
      (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).1
      (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT) index).2

abbrev TreeFamily := ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
  (preM := preM) (preT := preT) (postM := postM) (postT := postT) Request

section ObserverContext
variable {Context : Type} [Fintype Context]

abbrev ContextPrefix := Context × List (Observer.Event (QM := Bytes) (AM := Digest)
  (QT := QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (AT := Digest × C))

/-- The observer's private state is retained outside the protocol. Only
its selected canonical request enters the frontend and transcript. -/
def publicPrefix (requestOf : Context → Request)
    (earlier : ContextPrefix (C := C) binary prime primePlan repr shape setup (Context := Context)) : Prefix :=
  (requestOf earlier.1,earlier.2)

def windowContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) :=
  MerkleOracleWindow.window (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT)) trees

def finiteCodecContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) :=
  MerkleOracleWindow.finiteCodec (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT)) trees

def beforeContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) (H : Point → Digest × C) :=
  (MerkleOracleWindow.finiteResidual (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT)) trees (.inl ()) H).map Prod.fst

def laterContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context)
    (context : Context) (proof : Option Output) (H : Point → Digest × C) :=
  (MerkleOracleWindow.finiteResidual (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT)) trees (.inr (context,proof)) H).map Prod.fst

end ObserverContext

def windowForTrees (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
    (preM := preM) (preT := preT) (postM := postM) (postT := postT)) :=
  windowContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees

def finiteCodecForTrees (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
    (preM := preM) (preT := preT) (postM := postM) (postT := postT)) :=
  finiteCodecContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees

def beforeForTrees (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
    (preM := preM) (preT := preT) (postM := postM) (postT := postT)) (H : Point → Digest × C) :=
  beforeContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees H

def laterForTrees (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
    (preM := preM) (preT := preT) (postM := postM) (postT := postT))
    (request : Request) (proof : Option Output) (H : Point → Digest × C) :=
  laterContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees request proof H

def window := SHAObserverWindow.window SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after

def finiteCodec := SHAObserverWindow.finiteCodec SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after

omit [DecidableEq Observed] in
theorem finite_leaf_hash
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) (value) :
    HM ((finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside).leafEnc value) =
      OracleWindow.extend (window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) HM outside
        ((codec binary prime primePlan binaryNodes repr shape setup cfg).leafEnc value) :=
  MerkleOracleWindow.finite_leaf_hash (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT))
    (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after) HM outside value

omit [DecidableEq Observed] in
theorem finite_node_hash
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) (children) :
    HM ((finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside).nodeEnc children) =
      OracleWindow.extend (window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) HM outside
        ((codec binary prime primePlan binaryNodes repr shape setup cfg).nodeEnc children) :=
  MerkleOracleWindow.finite_node_hash (codec binary prime primePlan binaryNodes repr shape setup cfg)
    (ObserverWindow.budget (preM := preM) (preT := preT) (postM := postM) (postT := postT))
    (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after) HM outside children

def source (coins : FrontCoins) : HonestRuntime.Tape binary prime binaryNodes :=
  ⟨coins.1,coins.2,0,0⟩

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → N)
variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)

def cells (coins : FrontCoins) (priorState : Prefix) :=
  HonestRuntime.logical binary prime binaryNodes (original priorState.1) (remaining priorState.1)
    (source binary prime binaryNodes coins)

def front (coins : FrontCoins) (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) : Body :=
  let request := priorState.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let requested := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
    (source binary prime binaryNodes coins)
  let raw := HonestRuntime.frontendAtRoot b p primePlan binaryNodes repr shape setup
    (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
    binaryCount metadata (original request) (remaining request) request root H requested.frontend requested.selectors
  CompleteFrontendBody.rawBody b p primePlan root raw

def zeroStatement : JointResponse.Statement (First).participant (Second).participant :=
  (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)

def statements (coins : FrontCoins) (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  ((CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata priorState.1
    (front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins priorState labels) H).map (fun data => data.2.statement)).getD
    (zeroStatement binary prime primePlan binaryNodes repr shape setup cfg)

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def batching (coins : FrontCoins) (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) :=
  CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount metadata draw priorState.1
    (front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins priorState labels) H

variable (answer : Digest × C)

section ObserverContext
variable {Context : Type} [Fintype Context]
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)

def observerContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context)
    (priorState : ContextPrefix (C := C) binary prime primePlan repr shape setup (Context := Context))
    (publicView : Body × JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query (cfg.sample answer.2)).coordinates →
      (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
        MerkleCompiler.Leaf N (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0))
    (_labels : Fin (2*2443-1) → Digest)
    (opening : OpeningView 2443 (OrderedOpening.query (cfg.sample answer.2)).coordinates MerkleNonce Digest) :
    Merkle.RandomOracle.Tree {raw // raw ∈ windowContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees}
      Digest (Observer.View Bytes Digest Point (Digest × C) Context (Option Output) Observed) postM :=
  let completed := CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata (requestOf priorState.1) (cfg.sample answer.2)
    publicView.1 publicView.2 columns opening H answer
  let result : Option Output × (Point → Digest × C) :=
    match completed with | none => (none,H) | some result => (some result.1,result.2)
  (laterContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees
    priorState.1 result.1 result.2).map fun later => ⟨priorState.1,result.1,priorState.2,later.1,later.2⟩

def realContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) :=
  BackendCompiled.real BGeo NGeo
    (finiteCodecContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees)
    (beforeContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees H)
    postM (OrderedOpening.query (cfg.sample answer.2)) id
    (fun coins earlier => cells binary prime primePlan binaryNodes repr shape setup original remaining coins
      (publicPrefix binary prime primePlan repr shape setup requestOf earlier))
    (fun coins earlier labels => front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H draw
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (observerContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H answer requestOf trees)

def simulatedBackendContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) :=
  BackendCompiled.simulate BGeo NGeo
    (finiteCodecContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees)
    (beforeContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees H)
    postM (OrderedOpening.query (cfg.sample answer.2)) 0 id
    (fun coins earlier labels => front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H draw
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (observerContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H answer requestOf trees)

end ObserverContext

def observerForTrees
    (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT))
    (priorState : Prefix)
    (publicView : Body × JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query (cfg.sample answer.2)).coordinates →
      (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
        MerkleCompiler.Leaf N (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0))
    (_labels : Fin (2*2443-1) → Digest)
    (opening : OpeningView 2443 (OrderedOpening.query (cfg.sample answer.2)).coordinates MerkleNonce Digest) :
    Merkle.RandomOracle.Tree {raw // raw ∈ windowForTrees binary prime primePlan binaryNodes repr shape setup cfg trees}
      Digest (Observer.View Bytes Digest Point (Digest × C) Request (Option Output) Observed) postM :=
  observerContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H answer id trees
    priorState publicView columns _labels opening

def observer := observerForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H answer
  (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after)

def realForTrees
    (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT)) :=
  realContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H draw answer id trees

def real := realForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  original remaining H draw answer (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after)

def simulatedBackend := simulatedBackendContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  original remaining H draw answer id (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after)

local instance frontCoinsFintype : Fintype
    (CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) := inferInstance

local instance backendMasksFintype : Fintype
    (CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) := Fintype.ofFinite _

local instance genericBackendMasksFintype (bw nw s : ℕ) : Fintype
    (BackendCompiled.Masks (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
      (bw := bw) (nw := nw) (s := s)) := Fintype.ofFinite _

local instance merkleCoinsFintype : Fintype (MerklePreparation.Coins
    (Salt := MerkleNonce) (Digest := Digest)
    (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside}) 2443) := inferInstance

local instance coinsFintype : Fintype (BackendCompiled.Coins
    (FrontCoin := CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
    (Nonce := MerkleNonce) (D := Digest)
    (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside})
    (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (bw := rows binary.description.cells)
    (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)) := inferInstance

omit [DecidableEq Observed] in
theorem backend_hiding
    (satisfied : ∀ coins priorState labels,
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels).1.Satisfies (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup original remaining coins priorState).1) ∧
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels).2.Satisfies (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup original remaining coins priorState).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside original remaining H draw answer)
      (simulatedBackend binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside original remaining H draw answer) := by
  have codecInj := SHAObserverWindow.finiteCodec_inj SHAOracle.merkleDomain outside
    (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (MerkleRuntime.codec_inj (First).participant (Second).participant repr cfg.binaryField cfg.primeField setup.jointContext (by decide))
  have compiled := BackendCompiled.simulator_statClose BGeo NGeo
      (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
      (SHAObserverWindow.before SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after H)
      postM (OrderedOpening.query (cfg.sample answer.2)) 0 id
      (cells binary prime primePlan binaryNodes repr shape setup original remaining)
      (front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H)
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H)
      (batching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H draw)
      (observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer)
      (by decide) codecInj satisfied
  simp only [QuerySet.card_coordinates] at compiled
  convert compiled using 1 <;> rfl

def hashChecks (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) : Prop :=
  let request := priorState.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  ∀ responses coin converted,
    FullCoupling.hashChecks b p primePlan
      (CompleteSimulator.samples b p primePlan binaryNodes repr shape setup config)
      (CompleteSimulator.base b p primePlan binaryNodes repr shape setup config binaryCount metadata request root)
      H (FingerprintPrefix.context request root) (original request) responses coin converted

def frontSimulation (coins : CompleteSimulation.Coins binary prime) (priorState : Prefix)
    (labels : Fin (2*2443-1) → Digest) : Body :=
  let request := priorState.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let raw := CompleteSimulation.simulate b p primePlan
    (CompleteSimulator.samples b p primePlan binaryNodes repr shape setup config)
    (CompleteSimulator.base b p primePlan binaryNodes repr shape setup config binaryCount metadata request root)
    H (FingerprintPrefix.context request root)
    (RequestedSimulator.publicFrontendEquiv binary prime primePlan shape primeCount request coins)
  CompleteFrontendBody.body b p primePlan root raw

variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀ priorState labels,
  hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H priorState labels)

def frontendEquivAt (priorState : Prefix) (labels : Fin (2*2443-1) → Digest)
    (hashAt : hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H priorState labels) :
    FrontCoins ≃ CompleteSimulation.Coins binary prime :=
  let request := priorState.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  ((RequestedSimulator.privateFrontendEquiv binary prime primePlan shape primeCount request).prodCongr (Equiv.refl _)).trans
    ((FullCoupling.coupling b p primePlan
      (CompleteSimulator.samples b p primePlan binaryNodes repr shape setup config)
      (CompleteSimulator.base b p primePlan binaryNodes repr shape setup config binaryCount metadata request root)
      H (FingerprintPrefix.context request root) (original request) (remaining request) pivotOne hashAt
      (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))).trans
        (RequestedSimulator.publicFrontendEquiv binary prime primePlan shape primeCount request).symm)

def frontendEquiv (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) :
    FrontCoins ≃ CompleteSimulation.Coins binary prime :=
  frontendEquivAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H pivotOne priorState labels (validHash priorState labels)

omit [DecidableEq Observed] [DecidableEq B] [Fintype C] in
theorem front_equiv_at (priorState : Prefix) (labels : Fin (2*2443-1) → Digest)
    (hashAt : hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H priorState labels)
    (coins : FrontCoins) :
    frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
        (frontendEquivAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
          original remaining H pivotOne priorState labels hashAt coins) priorState labels =
      front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels := by
  let request := priorState.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  have actual := FullCoupling.coupling_view b p primePlan
    (CompleteSimulator.samples b p primePlan binaryNodes repr shape setup config)
    (CompleteSimulator.base b p primePlan binaryNodes repr shape setup config binaryCount metadata request root)
    H (FingerprintPrefix.context request root) (original request) (remaining request) pivotOne hashAt
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (RequestedSimulator.privateFrontendEquiv binary prime primePlan shape primeCount request coins.1) coins.2
  have encoded := congrArg (CompleteFrontendBody.rawBody b p primePlan root) actual.symm
  convert encoded using 1 <;> rfl

omit [DecidableEq Observed] [DecidableEq B] [Fintype C] in
theorem front_equiv (priorState : Prefix) (labels : Fin (2*2443-1) → Digest) (coins : FrontCoins) :
    frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
        (frontendEquiv binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
          original remaining H pivotOne validHash priorState labels coins) priorState labels =
      front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels :=
  front_equiv_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H pivotOne priorState labels (validHash priorState labels) coins

def publicStatements (coins : CompleteSimulation.Coins binary prime) (priorState : Prefix)
    (labels : Fin (2*2443-1) → Digest) :=
  ((CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata priorState.1
    (frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
      coins priorState labels) H).map (fun data => data.2.statement)).getD
    (zeroStatement binary prime primePlan binaryNodes repr shape setup cfg)

def publicBatching (coins : CompleteSimulation.Coins binary prime) (priorState : Prefix)
    (labels : Fin (2*2443-1) → Digest) :=
  CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount metadata draw priorState.1
    (frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
      coins priorState labels) H

section ObserverContext
variable {Context : Type} [Fintype Context]
variable (requestOf : Context → CanonicalRequest.Request shape binary.description.nPublic)

def simulatedPublicContextForTrees
    (trees : ContextTreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT) Context) :=
  BackendCompiled.simulate BGeo NGeo
    (finiteCodecContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees)
    (beforeContextForTrees binary prime primePlan binaryNodes repr shape setup cfg trees H)
    postM (OrderedOpening.query (cfg.sample answer.2)) 0 id
    (fun coins earlier labels => frontSimulation binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => publicStatements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (fun coins earlier labels => publicBatching binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H draw
      coins (publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
    (observerContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata H answer requestOf trees)

end ObserverContext

def simulatedPublicForTrees
    (trees : TreeFamily (C := C) (Observed := Observed) binary prime primePlan repr shape setup
      (preM := preM) (preT := preT) (postM := postM) (postT := postT)) :=
  simulatedPublicContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    H draw answer id trees

def simulatedPublic := simulatedPublicForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
  H draw answer (SHAObserverWindow.trees SHAOracle.merkleDomain outside prior after)

abbrev Shared := CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
  (CellLayout.Prime.cells prime.remaining prime.pads) ×
    MerklePreparation.Coins (Salt := MerkleNonce) (Digest := Digest)
      (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside}) 2443

def priorStateOf (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) : Prefix :=
  ((SHAObserverWindow.before SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after H).run shared.2.1).1

def dummyLabels (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) : Fin (2*2443-1) → Digest :=
  MerklePreparation.honestLabels
    (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)) 2443
    (SHAObserverWindow.before SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after H)
    (BackendCompiled.simMessages BGeo NGeo id shared.1) shared.2.2.1 shared.2.1

def fiber (shared : Shared binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    FrontCoins ≃ CompleteSimulation.Coins binary prime :=
  frontendEquiv binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
    pivotOne validHash (priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H shared)
    (dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H shared)

abbrev PrivateCoins := BackendCompiled.Coins (FrontCoin := CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B))
  (Nonce := MerkleNonce) (D := Digest)
  (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside})
  (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
  (bw := rows binary.description.cells) (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)

abbrev PublicCoins := BackendCompiled.Coins (FrontCoin := CompleteSimulation.Coins binary prime)
  (Nonce := MerkleNonce) (D := Digest)
  (Enc := {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside})
  (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
  (bw := rows binary.description.cells) (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads)) (s := 12)

/-- Only the frontend coins change. The backend tape, finite Merkle oracle,
nonces and auxiliary label tape remain fixed, so the dummy root is the same
parameter of both directions of this equivalence. -/
def frontendCoupling : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside where
  toFun coin := ((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    original remaining H pivotOne validHash (coin.1.2,coin.2) coin.1.1,coin.1.2),coin.2)
  invFun coin := (((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    original remaining H pivotOne validHash (coin.1.2,coin.2)).symm coin.1.1,coin.1.2),coin.2)
  left_inv coin := by
    change (((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
      original remaining H pivotOne validHash (coin.1.2,coin.2)).symm
      (fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining H pivotOne validHash (coin.1.2,coin.2) coin.1.1),coin.1.2),coin.2) = coin
    rw [Equiv.symm_apply_apply]
  right_inv coin := by
    change ((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
      original remaining H pivotOne validHash (coin.1.2,coin.2)
      ((fiber binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining H pivotOne validHash (coin.1.2,coin.2)).symm coin.1.1),coin.1.2),coin.2) = coin
    rw [Equiv.apply_symm_apply]

omit [DecidableEq Observed] in
theorem frontendCoupling_view
    (coin : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H draw answer
        (frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
          original remaining H pivotOne validHash coin) =
      simulatedBackend binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining H draw answer coin := by
  rcases coin with ⟨⟨frontend,backend⟩,merkle⟩
  have view := front_equiv binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H pivotOne validHash
    (priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle))
    (dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle)) frontend
  let earlier := priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle)
  let labels := dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (backend,merkle)
  let post := fun body : Body => BackendCompiled.runView
    (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    postM (OrderedOpening.query (cfg.sample answer.2)) id
    (observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer)
    earlier (MerkleBackend.simColumns BGeo NGeo backend)
    (body,MerkleBackend.simResponses BGeo NGeo (OrderedOpening.query (cfg.sample answer.2)) (0 : Fin 265)
      (((CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg binaryCount primeCount metadata earlier.1 body H).map
        (fun data => data.2.statement)).getD (zeroStatement binary prime primePlan binaryNodes repr shape setup cfg))
      (CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg binaryCount metadata draw earlier.1 body H) backend)
    merkle.2.1 merkle.1 labels
  convert congrArg post view using 1 <;> rfl

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem frontend_sameDistribution : SameDistribution
    (simulatedBackend binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
      original remaining H draw answer)
    (simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H draw answer) := by
  apply sameDistribution_of_equiv
    (frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
      original remaining H pivotOne validHash)
  intro coin
  exact (frontendCoupling_view binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    original remaining H draw answer pivotOne validHash coin).symm

include pivotOne validHash in
omit [DecidableEq Observed] in
/-- The joint backend masking and the complete frontend coin change compose
at the same fixed complete opening answer. The simulator endpoint contains
no witness cells, while the only algebraic premise is truth of the ordinary
compiled affine rows on the honest cells. -/
theorem simulator_statClose
    (satisfied : ∀ coins priorState labels,
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels).1.Satisfies (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup original remaining coins priorState).1) ∧
      (statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins priorState labels).2.Satisfies (Backend.logical (cells binary prime primePlan binaryNodes repr shape setup original remaining coins priorState).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside original remaining H draw answer)
      (simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H draw answer) := by
  have backend := backend_hiding binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount
    metadata prior after outside original remaining H draw answer satisfied
  have frontend := statClose_zero_of_equiv
    (frontendCoupling binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
      original remaining H pivotOne validHash)
    (fun coin => (frontendCoupling_view binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      prior after outside original remaining H draw answer pivotOne validHash coin).symm)
  have combined := backend.trans frontend
  simp only [add_zero] at combined
  convert combined using 1
  rfl

end LfzkV2.Current.ZeroKnowledge.BackendRuntime
