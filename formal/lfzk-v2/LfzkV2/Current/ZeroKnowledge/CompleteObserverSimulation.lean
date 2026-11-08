import LfzkV2.Current.ZeroKnowledge.CompleteObserver
import LfzkV2.Current.ZeroKnowledge.CompleteTerminal
import LfzkV2.Current.ZeroKnowledge.MerkleRuntimeTransport
import LfzkV2.Current.ZeroKnowledge.MerkleBackend
import LfzkV2.Current.ZeroKnowledge.CompletePublicBody
import LfzkV2.Current.ZeroKnowledge.MerkleRuntime
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment

/-! The backend hybrid's observer receives only public data: the frontend
body, both H/Z responses, the opened tuple columns and their authentication.
It constructs the current complete proof, programs the whole opening answer,
computes its final seal, and runs the original mixed post-proof observer.
Neither backend private masks nor unopened columns enter this constructor. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
local notation "Cfg" => CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R Cfg
local notation "Second" => RuntimeVerifier.second binary prime P R Cfg
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
local notation "Leaf" => (MerkleCompiler.Leaf B (ConcreteSetup.rows binary.cells) 0 ×
  MerkleCompiler.Leaf N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0)

theorem dummy_columns (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
    (CellLayout.Prime.cells prime.remaining prime.pads)) :
    (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant
      (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes)
        (Backend.profileGeometry primeNodes) tape i)) =
      CompleteVerifier.dummyColumns binary prime binaryNodes primeNodes Cfg tape := by
  funext i participant
  fin_cases participant <;> rfl

theorem batching_body (request : CanonicalRequest.Request shape binary.nPublic)
    (indices : Fin 84 ↪ Fin 2443) (frontend : Body)
    (response : JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opened : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest)
    (H : Point → Digest × C) :
    CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
      (CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend response columns opened) H =
      CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request
        { frontend with commitment := opened.rt } H := by
  simp only [CompleteCanonicalVerifier.batchingPoint,BackendPath.parent_point]
  exact CompleteTerminal.point_before repr shape setup binary.nPublic
    (CanonicalRuntime.binaryRequest binary prime P R repr shape setup
      (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount)
    metadata request cfg.initialLink
    ⟨{frontend with commitment := opened.rt},fun _ => 0⟩
    (CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend response columns opened)
    H g.batchingIndex.val (by rw [g.openingIndex_val]; omega)

theorem statementAt_body (request : CanonicalRequest.Request shape binary.nPublic)
    (indices : Fin 84 ↪ Fin 2443) (frontend : Body)
    (response : JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query indices).coordinates → Leaf)
    (opened : OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest)
    (H : Point → Digest × C) :
    CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request
      (CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend response columns opened) H =
      CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request
        { frontend with commitment := opened.rt } H := by
  unfold CompleteCanonicalVerifier.statementAt
  rw [batching_body binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata]

def opening (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce) (columns : Fin 2443 → Leaf) :
    OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest :=
  let scheme := (CompleteCanonicalVerifier.merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg).withOracle HM
  let values := fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)
  ⟨root scheme 2443 (fun i => (i,nonces i)) values,
    { nonce := fun i => nonces i.val
      frontierValue := fun vertex => commitLabels scheme 2443 (fun i => (i,nonces i)) values vertex.val }⟩

theorem body_honest (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce) (columns : Fin 2443 → Leaf)
    (frontend : Body) (response : JointResponse.Response (First).participant (Second).participant) :
    CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend response
        (fun i => columns i.val) (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces columns) =
      CompleteBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField
        cfg.binaryRows cfg.primeRows cfg.openings
        ((CompleteCanonicalVerifier.merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg).withOracle HM)
        indices nonces (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i))
        { frontend with commitment :=
          (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces columns).rt }
        (CompleteVerifier.wireResponses binary prime binaryNodes primeNodes Cfg response) setup.jointContext
        (by
          have bound := CompleteOpening.raw_frontier_bound
            ((CompleteCanonicalVerifier.merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg).withOracle HM)
            (fun i nonce => (i,nonce)) indices nonces
            (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i))
          exact bound.trans (by unfold OpeningBody.frontierCapacity; rw [cfg.openings,cfg.columns]; decide)) := by
  unfold CompleteObserver.body
  exact CompletePublicBody.fill_raw_honest (First).participant (Second).participant
    cfg.binaryField cfg.primeField cfg.binaryRows cfg.primeRows cfg.openings
    ((CompleteCanonicalVerifier.merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg).withOracle HM)
    indices nonces (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i))
    _ _ setup.jointContext _

theorem body_dummy (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) :
    CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend
      (CompleteBackend.responses binaryNodes primeNodes binary.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
        (OrderedOpening.query indices) statement coin tape)
      (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes)
        (Backend.profileGeometry primeNodes) tape i.val)
      (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces
        (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape)) =
      CompleteVerifier.simulatedBody binary prime binaryNodes primeNodes Cfg
        (CompleteCanonicalVerifier.merkleCodec binary prime binaryNodes primeNodes repr shape setup cfg)
        HM indices nonces tape statement coin frontend setup.jointContext := by
  rw [body_honest]
  unfold opening
  erw [dummy_columns binary prime binaryNodes primeNodes repr shape setup cfg tape]
  rfl

variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg))

def statement (request : CanonicalRequest.Request shape binary.nPublic)
    (frontend : Body) (H : Point → Digest × C) :
    JointResponse.Statement (First).participant (Second).participant :=
  ((CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg
    binaryCount primeCount metadata request frontend H).map (fun data => data.2.statement)).getD
      (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)

end LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation
