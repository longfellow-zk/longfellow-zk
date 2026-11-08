import LfzkV2.Current.ZeroKnowledge.BackendRuntime
import LfzkV2.Current.ZeroKnowledge.CompleteObserverCompletion
import LfzkV2.Current.ZeroKnowledge.MerkleRuntimeTransport
import LfzkV2.Current.ZeroKnowledge.BackendViewTransport

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeEncoding
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
-- The concrete heap has thousands of steps. Its input, root and opening
-- equalities are supplied by the symbolic transport lemmas below.
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run

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

def expanded (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) :
    Bytes → Digest := OracleWindow.extend
      (window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) HM outside

omit [DecidableEq Observed] in
theorem heap_value
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (nonces : Fin 2443 → MerkleNonce)
    (columns : Fin 2443 → (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
      MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0))
    (vertex : ℕ) (positive : 0 < vertex) :
    ((commitPass (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside))
      2443 nonces (fun i => (i,columns i)) (2*2443-1) (fun _ => default)).run HM).1 vertex =
      commitLabels ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg).withOracle (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM))
        2443 (fun i => (i,nonces i)) (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) vertex := by
  refine MerkleRuntimeTransport.pass_value_of_inputs
    (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)) HM
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes
      repr shape setup cfg).withOracle (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM))
    2443 nonces (fun i => (i,nonces i)) (fun i => (i,columns i))
    (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) ?_ ?_ vertex positive
  · intro i
    have hash := BackendRuntime.finite_leaf_hash binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM ((i,nonces i),columns i)
    simpa only [MerkleSimulation.nonceCodec,MerkleSimulation.shuffle,Equiv.coe_fn_mk,Codec.withOracle,CompleteCanonicalVerifier.merkleCodec,expanded,BackendRuntime.codec,MerkleRuntime.codec] using hash
  · intro children
    have hash := BackendRuntime.finite_node_hash binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM children
    simpa only [MerkleSimulation.nonceCodec,MerkleSimulation.shuffle,Equiv.coe_fn_mk,Codec.withOracle,CompleteCanonicalVerifier.merkleCodec,expanded,BackendRuntime.codec,MerkleRuntime.codec] using hash

omit [DecidableEq Observed] in
theorem committed_root
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (nonces : Fin 2443 → MerkleNonce)
    (columns : Fin 2443 → (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
      MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0)) :
    MerklePreparation.actualLabels
        (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside))
        2443 nonces (fun i => (i,columns i)) HM ⟨2*2443-2,by decide⟩ =
      root ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg).withOracle (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM))
        2443 (fun i => (i,nonces i)) (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) :=
  (BackendViewTransport.actualLabels_last
    (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside))
    (by decide : 0 < 2443) nonces (fun i => (i,columns i)) HM).trans
    (heap_value binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM nonces columns 1 (by decide))

omit [DecidableEq Observed] in
theorem heap_opening
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → MerkleNonce)
    (columns : Fin 2443 → (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
      MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0)) :
    (let values := ((commitPass (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside))
      2443 nonces (fun i => (i,columns i)) (2*2443-1) (fun _ => default)).run HM).1
    (⟨values 1,{ nonce := fun i => nonces i.val,frontierValue := fun vertex => values vertex.val }⟩ :
      OpeningView 2443 (OrderedOpening.query indices).coordinates MerkleNonce Digest)) =
      CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) indices nonces columns := by
  exact MerkleRuntimeTransport.openingView_eq_of_labels 2443 (OrderedOpening.query indices).coordinates nonces
    (((commitPass (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside))
      2443 nonces (fun i => (i,columns i)) (2*2443-1) (fun _ => default)).run HM).1)
    (commitLabels ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes
      repr shape setup cfg).withOracle (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM))
      2443 (fun i => (i,nonces i)) (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)))
    (heap_value binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM nonces columns)

omit [DecidableEq Observed] in
theorem observer_output
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (priorState : Prefix)
    (publicView : Body × JointResponse.Response (First).participant (Second).participant)
    (columns : ↥(OrderedOpening.query (cfg.sample answer.2)).coordinates →
      (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
        MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0))
    (labels : Fin (2*2443-1) → Digest)
    (opened : OpeningView 2443 (OrderedOpening.query (cfg.sample answer.2)).coordinates MerkleNonce Digest) :
    ((BackendRuntime.observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      prior after outside H answer priorState publicView columns labels opened).run HM).1 =
      CompleteSimulator.observeCompletion binary prime primePlan repr shape setup after priorState.1 priorState.2
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H
        (CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
          binaryCount primeCount metadata priorState.1 (cfg.sample answer.2) publicView.1 publicView.2 columns opened H answer) := by
  let completed := CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata priorState.1 (cfg.sample answer.2) publicView.1 publicView.2 columns opened H answer
  let result : Option Output × (Point → Digest × C) :=
    match completed with | none => (none,H) | some value => (some value.1,value.2)
  let decorate := fun later : Observed × Trace =>
    (⟨priorState.1,result.1,priorState.2,later.1,later.2⟩ : Observer.View Bytes Digest Point (Digest × C) Request (Option Output) Observed)
  have mapped := congrArg Prod.fst (Merkle.RandomOracle.Tree.run_map
    (SHAObserverWindow.later SHAOracle.merkleDomain outside
      (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after priorState.1 result.1 result.2) decorate HM)
  have later := congrArg decorate (SHAObserverWindow.later_output SHAOracle.merkleDomain outside
    (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after
    (codec_leaf_domain binary prime primePlan binaryNodes repr shape setup cfg)
    (codec_node_domain binary prime primePlan binaryNodes repr shape setup cfg)
    priorState.1 result.1 HM result.2)
  exact mapped.trans later

omit [DecidableEq Observed] in
set_option backward.isDefEq.respectTransparency false in
theorem runView_output
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (priorState : Prefix)
    (publicView : Body × JointResponse.Response (First).participant (Second).participant)
    (columns : Fin 2443 → (MerkleCompiler.Leaf B (rows binary.description.cells) 0 ×
      MerkleCompiler.Leaf Adapter.Mdoc.P (rows (CellLayout.Prime.cells prime.remaining prime.pads)) 0))
    (nonces : Fin 2443 → MerkleNonce) (labels : Fin (2*2443-1) → Digest) :
    BackendCompiled.runView (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
      postM (OrderedOpening.query (cfg.sample answer.2)) id
      (BackendRuntime.observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer)
      priorState columns publicView nonces HM labels =
      CompleteSimulator.observeCompletion binary prime primePlan repr shape setup after priorState.1 priorState.2
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H
        (CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
          binaryCount primeCount metadata priorState.1 (cfg.sample answer.2) publicView.1 publicView.2 (fun i => columns i.val)
          (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
            (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) (cfg.sample answer.2) nonces columns) H answer) := by
  have matching := heap_opening binary prime primePlan binaryNodes repr shape setup cfg prior after outside
    HM (cfg.sample answer.2) nonces columns
  have changed := BackendViewTransport.runView_of_opening
    (r := 84) (w := 265) (s := 12) (n := 2443)
    (bw := rows binary.description.cells) (nw := rows (CellLayout.Prime.cells prime.remaining prime.pads))
    (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    postM (OrderedOpening.query (cfg.sample answer.2))
    (BackendRuntime.observer binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside H answer)
    priorState columns publicView nonces HM labels
    (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) (cfg.sample answer.2) nonces columns) matching
  exact changed.trans (observer_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside HM H answer priorState publicView (fun i => columns i.val) labels
    (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) (cfg.sample answer.2) nonces columns))

def simulatorTape (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    CompleteSimulator.Tape (C := C) binary prime binaryNodes where
  frontend := coin.1.1
  backend := coin.1.2
  nonces := coin.2.2.1
  answer := answer

omit [DecidableEq Observed] [Fintype C] in
theorem requested_commitment (request : Request) (HM : Bytes → Digest)
    (tape : CompleteSimulator.Tape (C := C) binary prime binaryNodes) :
    CompleteSimulator.commitment
      (RequestedSimulator.requestedBinary binary prime primePlan shape request)
      (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request)
      primePlan binaryNodes repr shape setup
      (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request) HM
      (RequestedSimulator.tape binary prime primePlan binaryNodes shape primeCount request tape) =
      CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg HM tape := rfl

omit [DecidableEq Observed] in
set_option backward.isDefEq.respectTransparency false in
theorem dummy_root (H : Point → Digest × C) (answer : Digest × C)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    BackendRuntime.dummyLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside H
        (coin.1.2,coin.2) ⟨2*2443-2,by decide⟩ =
      CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
        (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) := by
  have value := committed_root binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1 coin.2.2.1
    (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) coin.1.2)
  have columns := CompleteObserverSimulation.dummy_columns binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg coin.1.2
  have rooted := congrArg (fun columns => root
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1))
      2443 (fun i => (i,coin.2.2.1 i)) columns) columns
  have right : CompleteSimulator.commitment binary prime primePlan binaryNodes repr shape setup cfg
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
      (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside answer coin) =
      root ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg).withOracle
          (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1))
        2443 (fun i => (i,coin.2.2.1 i))
        (CompleteVerifier.dummyColumns binary.description prime binaryNodes ConcreteSetup.primeNodes Public coin.1.2) := rfl
  exact value.trans (rooted.trans right.symm)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeEncoding
