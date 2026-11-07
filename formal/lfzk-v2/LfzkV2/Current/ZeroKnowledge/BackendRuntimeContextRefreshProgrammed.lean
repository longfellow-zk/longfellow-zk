import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRefreshView
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextEncoding
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshResult
import LfzkV2.Current.ZeroKnowledge.OracleRefreshObservation
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRefreshedKey

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntimeContext BackendRuntimeReal
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run TranscriptV2.Chain.point TranscriptV2.Chain.replay Option.map
attribute [local irreducible] BackendRuntimeContext.window BackendRuntimeContext.expanded
  CompleteSimulator.samples OracleHonestCanonical.writer OracleHonestCanonical.root
  OracleHonestRuntime.pending FullCoupling.hashChecks
attribute [local irreducible] OracleHonestTree.tree OracleHonestTree.asPending OracleHonestTree.input
  OracleHonestRuntime.finish BackendRuntimeContextEncoding.observeCompletion refreshedForRequest Observer.run

variable {B C Context Observed : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [Fintype Context] [DecidableEq Observed]
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
private theorem observe_total
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (H : Point → Digest × C) (earlier : Prefix) (completed : Option (Output × (Point → Digest × C))) :
    BackendRuntimeContextEncoding.observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H completed =
      let total := OracleResults.totalize
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H completed
      refreshObserve binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM earlier total.1 total.2.2 := by
  unfold BackendRuntimeContextEncoding.observeCompletion refreshObserve OracleResults.totalize
  cases completed <;> rfl

omit [DecidableEq Observed] in
theorem refreshed_observation_stored (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (sample : Fin 361 → B)
    (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM)
      (requestOf ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1.1) H sample) :
    let fullHM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
    let earlier := ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1
    let request := requestOf earlier.1
    let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
    let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
    let configuration := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request
      (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    BackendRuntimeContextEncoding.observeCompletion binary prime primePlan repr shape setup after
      earlier.1 earlier.2 fullHM H
      (refreshedForRequest b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata draw
        (original request) (remaining request) source sample request fullHM H answer) =
      programmedView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside original remaining draw frame HM (sample,(H,answer)) := by
  let fullHM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
  let earlier := ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1
  let template := OracleHonestCoins.assemble binary prime binaryNodes frame 0
  let request := requestOf earlier.1
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let configuration := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request template
  let current := ((OracleHonestTree.tree b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata
    (original request) (remaining request) source request fullHM draw sample).run H).1
  have hash' := hash
  change OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM request H sample at hash'
  unfold OracleHonestRefresh.hashChecks at hash'
  have pending := OracleHonestTree.pending_output b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata
    (original request) (remaining request) source request fullHM draw H sample pivotOne hash'
  unfold programmedView OracleHonestRefresh.programmed OracleRefreshProbability.programmed OracleRefreshActive.programmed
  simp only [OracleRefreshPrior.program,OracleRefreshCompose.append_run,OracleHonestRefresh.observation,
    OracleRefreshPrior.target,OracleRefreshPrior.enabled]
  have finishRule := OracleHonestRefresh.finish_next_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw (requestOf ∘ Prod.fst) sample earlier H
  have activeRule := OracleHonestRefresh.active_next_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw (requestOf ∘ Prod.fst) sample earlier H
  have inputRule := OracleHonestRefresh.input_next_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw (requestOf ∘ Prod.fst) sample earlier H
  rw [finishRule]
  let response := OracleHonestTree.asPending b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata
    (original request) (remaining request) source request fullHM draw sample current
  let nextState := ((OracleHonestRefresh.next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw (requestOf ∘ Prod.fst) sample earlier).run H).1
  let enabled := OracleHonestRefresh.active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw sample nextState
  let nativeInput := OracleHonestRefresh.input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM sample nextState
  let selected := if enabled then Function.update H nativeInput answer else H
  let sourceKey := OracleHonestTree.input b p primePlan binaryNodes repr shape setup configuration binaryCount metadata
    (original request) (remaining request) source request fullHM sample current
  let key := refreshedKey b p primePlan binaryNodes repr shape setup configuration binaryCount metadata request H
  let finish := fun proof oracle => OracleHonestRuntime.finish b p primePlan binaryNodes repr shape setup configuration binaryCount metadata
    (original request) (remaining request) source request fullHM oracle sample proof
  let observe := refreshObserve binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM earlier
  let complete := fun (proofs : Option (CanonicalRequest.Output (g := CompleteSimulation.geometry b p primePlan) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))) => proofs.map
    (refreshedCallback b p primePlan binaryNodes repr shape setup configuration binaryCount metadata
      (original request) (remaining request) source sample request fullHM H answer)
  have correct : ∀ proof, response = some proof → sourceKey = key proof := by
    intro proof same
    have parsed := pending.symm.trans same
    have fact := pending_refreshed_key b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata
      (original request) (remaining request) source request fullHM draw H sample pivotOne hash' proof parsed
    exact fact
  have completed : refreshedForRequest b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata draw
      (original request) (remaining request) source sample request fullHM H answer = complete response := by
    unfold refreshedForRequest
    change complete (OracleHonestRuntime.pending b p primePlan binaryNodes repr shape setup configuration binaryCount primeCount metadata
      (original request) (remaining request) source request fullHM H draw sample) = complete response
    exact congrArg complete pending.symm
  have observed := congrArg (BackendRuntimeContextEncoding.observeCompletion binary prime primePlan repr shape setup after earlier.1 earlier.2 fullHM H) completed
  have total := observe_total binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM H earlier (complete response)
  have aborted : response = none → selected = H := by
    intro none
    have disabled : ¬enabled := by
      intro active
      have some := activeRule.mp active
      change response.isSome at some
      rw [none] at some
      contradiction
    exact if_neg disabled
  have successful : ∀ proof, response = some proof → selected = Function.update H (key proof) answer := by
    intro proof same
    have present : response.isSome := by rw [same]; rfl
    have active : enabled := activeRule.mpr present
    have point : nativeInput = key proof := inputRule.trans (correct proof same)
    exact (if_pos active).trans (congrArg (fun point => Function.update H point answer) point)
  have law := OracleRefreshObservation.totalize_map_selected response fullHM H answer key finish observe selected aborted successful
  have packed : complete response = response.map (fun proof =>
      let oracle := Function.update H (key proof) answer
      (finish proof oracle,oracle)) := by
    unfold complete
    apply congrArg (fun callback => response.map callback)
    funext proof
    unfold refreshedCallback
    rfl
  have totalPacked := congrArg (fun completed =>
    let result := OracleResults.totalize fullHM H completed
    observe result.1 result.2.2) packed
  have final := totalPacked.trans law
  exact observed.trans (total.trans final)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
