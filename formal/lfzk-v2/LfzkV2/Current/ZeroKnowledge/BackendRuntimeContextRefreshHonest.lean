import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRefreshView

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntimeContext
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run

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

omit [DecidableEq Observed] [Fintype C] [Fintype Context] in
private theorem requested_oracles (request : Request) (tape : HonestRuntime.Tape binary prime binaryNodes)
    (HM : Bytes → Digest) (H : Point → Digest × C) :
    (RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      request (original request) (remaining request) tape HM H).2 = (HM,H) := rfl

attribute [local irreducible] RequestedExperiment.honestForRequest HonestRuntime.prove OracleHonestRefresh.finish

omit [DecidableEq Observed] in
theorem honestView_eq_requested (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (H : Point → Digest × C) (answer : Digest × C) (sample : Fin 361 → B)
    (pivotOne : binary.basis 0 = 1)
    (hash : OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM)
      (requestOf ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1.1) H sample) :
    honestView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        requestOf prior after outside original remaining draw frame HM (sample,(H,answer)) =
      RequestedContextExperiment.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        requestOf prior after original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame sample)
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H := by
  let fullHM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM
  let template := OracleHonestCoins.assemble binary prime binaryNodes frame 0
  let actualTape := OracleHonestCoins.assemble binary prime binaryNodes frame sample
  let earlier := ((refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM).run H).1
  let viewOf := fun priorState : Prefix =>
    refreshObserve binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM priorState
      (RequestedExperiment.honestForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        (requestOf priorState.1) (original (requestOf priorState.1)) (remaining (requestOf priorState.1)) actualTape fullHM H).1 H
  have finished := OracleHonestRefresh.finish_next binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining template fullHM draw (requestOf ∘ Prod.fst) sample earlier H pivotOne hash
  have tapeEq : OracleHonestRuntime.tapeAt binary prime binaryNodes template sample = actualTape := rfl
  rw [tapeEq] at finished
  have stored : honestView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside original remaining draw frame HM (sample,(H,answer)) = viewOf earlier := by
    unfold honestView OracleHonestRefresh.honest OracleRefreshProbability.honest OracleRefreshActive.honest
    simp only [OracleRefreshPrior.program,OracleRefreshCompose.append_run,OracleHonestRefresh.observation]
    rw [finished]
    rfl
  have prefixEq : earlier = Observer.run fullHM H prior :=
    congrArg Prod.fst (Observer.fixMerkle_run H fullHM prior)
  have moved := congrArg viewOf prefixEq
  have actual : viewOf (Observer.run fullHM H prior) =
      RequestedContextExperiment.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        requestOf prior after original remaining actualTape fullHM H := by
    simp only [viewOf,refreshObserve,RequestedContextExperiment.honest,ObserverStateful.experiment,ObserverStateful.callback,Observer.experiment,requested_oracles]
    rfl
  exact stored.trans (moved.trans actual)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
