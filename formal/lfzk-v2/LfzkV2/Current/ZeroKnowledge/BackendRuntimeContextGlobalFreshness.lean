import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobalSimulator
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRefreshView
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshBound

/-! At each fixed full SHA oracle, refresh the complete opening answer
using the independent primary mask, then average over the other source
coins and that same larger table. Witness validity is used only at the
actual earlier request under its fixed complementary SHA slice. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
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

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)

attribute [local instance] OracleHonestCoins.frameFintype
attribute [local irreducible] OracleHonestRefresh.hashChecks FullCoupling.hashChecks

variable (large : Finset Bytes)
variable (contains : BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside ⊆ large)
variable (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)
variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀ (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
    (earlier : Context × List (Observer.Event (QM := Bytes) (AM := Digest)
      (QT := QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (AT := Digest × C))) labels,
  BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
  BackendRuntime.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H
    (BackendRuntime.publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)
variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)

include onlyMerkle in
theorem merge_oracle (table : Table large) :
    SHAOracle.merge SHAOracle.merkleDomain outside (oracle outside large table) = oracle outside large table := by
  funext raw
  by_cases member : SHAOracle.merkleDomain raw
  · simp only [SHAOracle.merge,if_pos member]
  · simp only [SHAOracle.merge,if_neg member]
    exact (oracle_complement outside large onlyMerkle table raw member).symm

include onlyMerkle validHash in
omit [Fintype C] [Fintype Context] [DecidableEq Observed] in
theorem hash_at_run (table : Table large) (tape : HonestRuntime.Tape binary prime binaryNodes)
    (H : Point → Digest × C) (sample : Fin 361 → B) :
    OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape
      (oracle outside large table) (requestOf (Observer.run (oracle outside large table) H prior).1) H sample := by
  let HM := oracle outside large table
  let earlier := Observer.run HM H prior
  let request := requestOf earlier.1
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape
  let value := OracleHonestCanonical.root b p primePlan binaryNodes repr shape setup config (original request) (remaining request) source HM sample
  have reachable : BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside request := by
    refine ⟨HM,H,?_⟩
    rw [merge_oracle outside large onlyMerkle table]
  have applicable := validHash H earlier (fun _ => value) reachable
  unfold OracleHonestRefresh.hashChecks
  simpa only [BackendRuntime.hashChecks,BackendRuntime.publicPrefix,OracleHonestCanonical.writer] using applicable

include onlyMerkle validHash pivotOne fits bodyFits in
omit [DecidableEq Observed] in
theorem freshness_fixed (table : Table large) (frame : OracleHonestCoins.Frame binary prime binaryNodes) :
    StatClose ((preT : ℚ)/(2 : ℚ)^46208)
      (BackendRuntimeContextReal.programmedView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
        (oracle outside large table) original remaining draw frame (fun raw => oracle outside large table raw.val))
      (BackendRuntimeContextReal.honestView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
        (oracle outside large table) original remaining draw frame (fun raw => oracle outside large table raw.val)) := by
  unfold BackendRuntimeContextReal.programmedView BackendRuntimeContextReal.honestView
    BackendRuntimeContextReal.refreshBefore BackendRuntimeContextReal.refreshObserve
  simp only [expanded_self]
  let observe : Prefix → Option Output → (Point → Digest × C) →
      Observer.View Bytes Digest Point (Digest × C) Context (Option Output) Observed :=
    fun earlier proof returned =>
      let later := Observer.run (oracle outside large table) returned (after earlier.1 proof)
      ⟨earlier.1,proof,earlier.2,later.1,later.2⟩
  have truthful : ∀ (H : Point → Digest × C) (sample : Fin 361 → B),
      OracleHonestRefresh.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0) (oracle outside large table)
        ((requestOf ∘ Prod.fst) ((Observer.fixMerkle (oracle outside large table) prior).run H).1) H sample := by
    intro H sample
    have h := hash_at_run binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior outside
      original remaining large onlyMerkle validHash table (OracleHonestCoins.assemble binary prime binaryNodes frame 0) H sample
    simpa only [Function.comp_apply,Observer.fixMerkle_run] using h
  have law := OracleHonestRefresh.statClose binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining
    (OracleHonestCoins.assemble binary prime binaryNodes frame 0) (oracle outside large table) draw (requestOf ∘ Prod.fst)
    (Observer.fixMerkle (oracle outside large table) prior) observe fits bodyFits pivotOne truthful
  exact Probability.changeFintype law

@[irreducible] def programmed
    (coin : (BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large) ×
      BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :=
  BackendRuntimeContextReal.programmedView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
    (oracle outside large coin.1.2) original remaining draw coin.1.1.1 (fun raw => oracle outside large coin.1.2 raw.val) coin.2

@[irreducible] def sourceHonest
    (coin : (BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large) ×
      BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :=
  BackendRuntimeContextReal.honestView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
    (oracle outside large coin.1.2) original remaining draw coin.1.1.1 (fun raw => oracle outside large coin.1.2 raw.val) coin.2

include onlyMerkle validHash pivotOne fits bodyFits in
omit [DecidableEq Observed] in
theorem freshness :
    StatClose ((preT : ℚ)/(2 : ℚ)^46208)
      (programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large)
      (sourceHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large) := by
  have mixed := statClose_mix (by positivity : 0 ≤ (preT : ℚ)/(2 : ℚ)^46208)
    (fun outer : BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large =>
      BackendRuntimeContextReal.programmedView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
        (oracle outside large outer.2) original remaining draw outer.1.1 (fun raw => oracle outside large outer.2 raw.val))
    (fun outer : BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large =>
      BackendRuntimeContextReal.honestView binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after
        (oracle outside large outer.2) original remaining draw outer.1.1 (fun raw => oracle outside large outer.2 raw.val))
    (fun outer => freshness_fixed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      draw original remaining large onlyMerkle pivotOne validHash fits bodyFits outer.2 outer.1.1)
  unfold programmed sourceHonest
  exact Probability.changeFintype mixed

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
