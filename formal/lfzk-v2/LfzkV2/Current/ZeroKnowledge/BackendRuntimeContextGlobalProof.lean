import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobalFreshness
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRealProgrammed
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextRefreshHonest

/-! Complete stateful-protocol composition at one fixed global Merkle
window. The final endpoints are the actual honest prover and actual
witness-free simulator, sharing that one full SHA oracle and retaining
the private observer context and both full mixed traces. -/
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
local notation "FrontCoins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)

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

include onlyMerkle validHash pivotOne in
omit [DecidableEq Observed] in
theorem real_global
    (coin : (BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large) ×
      BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :
    realFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large contains
        ((BackendRuntimeGlobalCoins.refreshEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)).symm coin) =
      programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large coin := by
  rcases coin with ⟨⟨frame,table⟩,challenges⟩
  let HM := oracle outside large table
  let tape := OracleHonestCoins.assemble binary prime binaryNodes frame.1 challenges.1
  have agree : ∀ raw, ¬SHAOracle.merkleDomain raw → outside raw = HM raw := by
    intro raw off
    exact (oracle_complement outside large onlyMerkle table raw off).symm
  have transported := BackendRuntimeContextOutside.real_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after draw original remaining outside HM agree HM challenges.2.1 challenges.2.2
    (tape.frontend,tape.selectors) tape.backend tape.nonces frame.2
  have truthful := hash_at_run binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior outside
    original remaining large onlyMerkle validHash table (OracleHonestCoins.assemble binary prime binaryNodes frame.1 0) challenges.2.1 challenges.1
  have endpoint := BackendRuntimeContextReal.real_eq_programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after HM original remaining draw frame.1 (fun raw => HM raw.val) frame.2 challenges.2.1 challenges.2.2 challenges.1 pivotOne
    (by simpa only [expanded_self] using truthful)
  rw [BackendRuntimeGlobalCoins.refreshEquiv_symm]
  unfold realFinite realLocal programmed
  rw [restrict_oracle]
  exact transported.trans endpoint

include onlyMerkle validHash pivotOne in
omit [DecidableEq Observed] in
theorem honest_global
    (coin : (BackendRuntimeGlobalCoins.Frame binary prime binaryNodes × Table large) ×
      BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :
    sourceHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large coin =
      honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large
        (BackendRuntimeGlobalCoins.privateTranscriptEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)
          ((BackendRuntimeGlobalCoins.refreshEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)).symm coin)) := by
  rcases coin with ⟨⟨frame,table⟩,challenges⟩
  let HM := oracle outside large table
  have truthful := hash_at_run binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior outside
    original remaining large onlyMerkle validHash table (OracleHonestCoins.assemble binary prime binaryNodes frame.1 0) challenges.2.1 challenges.1
  have endpoint := BackendRuntimeContextReal.honestView_eq_requested binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after HM original remaining draw frame.1 (fun raw => HM raw.val) challenges.2.1 challenges.2.2 challenges.1 pivotOne
    (by simpa only [BackendRuntimeContextReal.refreshBefore,expanded_self,Observer.fixMerkle_run] using truthful)
  rw [expanded_self] at endpoint
  unfold sourceHonest honest
  rw [BackendRuntimeGlobalCoins.refreshEquiv_symm]
  simpa only [BackendRuntimeGlobalCoins.privateTranscriptEquiv,BackendRuntimeRegroup.transcriptLast,Equiv.coe_fn_mk,
    BackendRuntimeGlobalCoins.honestTape,Equiv.apply_symm_apply] using endpoint

include onlyMerkle validHash pivotOne fits bodyFits in
omit [DecidableEq Observed] in
theorem opening_refresh :
    StatClose ((preT : ℚ)/(2 : ℚ)^46208)
      (fun coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large =>
        honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large
          (BackendRuntimeGlobalCoins.privateTranscriptEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large) coin))
      (realFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large contains) := by
  let e := BackendRuntimeGlobalCoins.refreshEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)
  have source (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large) :
      honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large
          (BackendRuntimeGlobalCoins.privateTranscriptEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large) coin) =
        sourceHonest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large (e coin) := by
    have same := honest_global binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      draw original remaining large onlyMerkle pivotOne validHash (e coin)
    simpa only [e,Equiv.symm_apply_apply] using same.symm
  have target (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large) :
      realFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large contains coin =
        programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large (e coin) := by
    have same := real_global binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      draw original remaining large contains onlyMerkle pivotOne validHash (e coin)
    simpa only [e,Equiv.symm_apply_apply] using same
  have law := freshness binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
    draw original remaining large onlyMerkle pivotOne validHash fits bodyFits
  exact Probability.changeFintype (statClose_reindex e e source target law.symm)

include contains onlyMerkle validHash pivotOne fits bodyFits in
omit [DecidableEq Observed] in
theorem statClose
    (satisfied : ∀ (H : Point → Digest × C) (coins : FrontCoins) (earlier : Prefix) labels,
      BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).1.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).1) ∧
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).2.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM + (preT : ℚ)/(2 : ℚ)^46208)
      (honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large)
      (simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large) := by
  have first := opening_refresh binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
    draw original remaining large contains onlyMerkle pivotOne validHash fits bodyFits
  have second := backend_lift binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
    draw original remaining pivotOne validHash large contains satisfied
  have combined := first.trans second
  rw [add_comm ((preT : ℚ)/(2 : ℚ)^46208)] at combined
  let realOrder := BackendRuntimeGlobalCoins.privateTranscriptEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)
  let simOrder := BackendRuntimeGlobalCoins.publicTranscriptEquiv (C := C) binary prime primePlan binaryNodes repr shape setup (Table large)
  have source (coin) :
      honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large coin =
        honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large
          (realOrder (realOrder.symm coin)) := by rw [Equiv.apply_symm_apply]
  have target (coin) :
      simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large coin =
        simulateFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large contains
          (simOrder.symm coin) := by
    have same := simulator_global binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside
      draw large contains onlyMerkle (simOrder.symm coin)
    simpa only [simOrder,Equiv.apply_symm_apply] using same.symm
  exact Probability.changeFintype (statClose_reindex realOrder.symm simOrder.symm source target combined)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
