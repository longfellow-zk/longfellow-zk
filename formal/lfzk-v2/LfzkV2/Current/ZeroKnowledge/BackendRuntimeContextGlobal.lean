import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeGlobalCoins
import LfzkV2.Current.ZeroKnowledge.SHAGlobalWindow
import LfzkV2.Current.ZeroKnowledge.Error
import LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment

/-! Stateful complete-protocol experiments over one fixed Merkle marginal.
The prover coin spaces and final transcript-table factor are independent of
raw-oracle complements. All validity premises are scoped to actual requests
under the same complementary SHA oracle. -/
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

abbrev PrivateOuter := BackendRuntimeRegroup.PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup
abbrev PublicOuter := BackendRuntimeRegroup.PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup
abbrev LocalTable := {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest

def realLocal (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    LocalTable binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining
    coin.1.1.1 coin.1.1.2 (coin.1.2.1,(coin.2,coin.1.2.2))

def simulateLocal (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    LocalTable binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw
    coin.1.1.1 coin.1.1.2 (coin.1.2.1,(coin.2,coin.1.2.2))

private def backendOrder {OracleSpace OuterSpace TableSpace RestSpace : Type} :
    (OracleSpace × (OuterSpace × (TableSpace × RestSpace))) ≃ ((OracleSpace × OuterSpace × RestSpace) × TableSpace) where
  toFun coin := ((coin.1,coin.2.1,coin.2.2.2),coin.2.2.1)
  invFun coin := (coin.1.1,(coin.1.2.1,coin.2,coin.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀ (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
    (earlier : Context × List (Observer.Event (QM := Bytes) (AM := Digest)
      (QT := QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (AT := Digest × C))) labels,
  BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
  BackendRuntime.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original H
    (BackendRuntime.publicPrefix binary prime primePlan repr shape setup requestOf earlier) labels)

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem mixed_hiding
    (satisfied : ∀ (H : Point → Digest × C) (coins : FrontCoins) (earlier : Prefix) labels,
      BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).1.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).1) ∧
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).2.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (realLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining)
      (simulateLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw) := by
  have nonnegative := Error.nonnegative (Fintype.card Digest) (Fintype.card Digest) 2 2443 84 preM postM 0
  simp only [Error.bound,Nat.cast_zero,zero_div,add_zero] at nonnegative
  let first := fun (oracle : BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup)
      (coin : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) =>
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining oracle.1 oracle.2 coin
  let second := fun (oracle : BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup)
      (coin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) =>
    BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw oracle.1 oracle.2 coin
  have each (oracle : BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup) :
      StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
        MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM) (first oracle) (second oracle) := by
    exact Probability.changeFintype (BackendRuntimeContext.simulator_statClose binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside draw original remaining oracle.1 oracle.2 pivotOne (validHash oracle.1) (satisfied oracle.1))
  have mixed := statClose_mix nonnegative first second each
  exact Probability.changeFintype (statClose_reindex backendOrder.symm backendOrder.symm (fun _ => rfl) (fun _ => rfl) mixed)

private def restrictTable {Raw Value : Type} (small large : Finset Raw) (contains : small ⊆ large)
    (table : {raw // raw ∈ large} → Value) : {raw // raw ∈ small} → Value :=
  fun raw => table ⟨raw.val,contains raw.property⟩

private theorem restrictTable_extend {Raw Value : Type} [DecidableEq Raw]
    (small large : Finset Raw) (contains : small ⊆ large)
    (table : {raw // raw ∈ large} → Value) (outside : Raw → Value) :
    restrictTable small large contains table = fun raw => OracleWindow.extend large table outside raw.val := by
  funext raw
  exact (OracleWindow.extend_mem large table outside raw.val (contains raw.property)).symm

variable (large : Finset Bytes)
variable (contains : BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside ⊆ large)
variable (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)

abbrev Table := {raw // raw ∈ large} → Digest

def oracle (table : Table large) : Bytes → Digest := OracleWindow.extend large table outside

def restrict (table : Table large) : LocalTable binary prime primePlan binaryNodes repr shape setup cfg prior after outside :=
  restrictTable (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) large contains table

omit [DecidableEq Observed] in
theorem restrict_oracle (table : Table large) :
    restrict binary prime primePlan binaryNodes repr shape setup cfg prior after outside large contains table =
      fun raw => oracle outside large table raw.val := by
  exact restrictTable_extend (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    large contains table outside

include onlyMerkle in
theorem oracle_complement (table : Table large) (raw : Bytes) (off : ¬SHAOracle.merkleDomain raw) :
    oracle outside large table raw = outside raw := by
  have absent : raw ∉ large := fun member => off (onlyMerkle raw member)
  unfold oracle OracleWindow.extend
  exact dif_neg absent

@[irreducible] def realFinite
    (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large) :=
  realLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining
    (coin.1,restrict binary prime primePlan binaryNodes repr shape setup cfg prior after outside large contains coin.2)

@[irreducible] def simulateFinite
    (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large) :=
  simulateLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw
    (coin.1,restrict binary prime primePlan binaryNodes repr shape setup cfg prior after outside large contains coin.2)

@[irreducible] def honest
    (coin : (BackendRuntimeGlobalCoins.PrivateProver (C := C) binary prime binaryNodes × Table large) × (Point → Digest × C)) :=
  RequestedContextExperiment.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw requestOf prior after original remaining
    (BackendRuntimeGlobalCoins.honestTape binary prime binaryNodes coin.1) (oracle outside large coin.1.2) coin.2

@[irreducible] def simulate
    (coin : (BackendRuntimeGlobalCoins.PublicProver (C := C) binary prime binaryNodes × Table large) × (Point → Digest × C)) :=
  RequestedContextExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw requestOf prior after
    (BackendRuntimeGlobalCoins.simulatorTape binary prime binaryNodes coin.1) (oracle outside large coin.1.2) coin.2

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem backend_lift
    (satisfied : ∀ (H : Point → Digest × C) (coins : FrontCoins) (earlier : Prefix) labels,
      BackendRuntimeContext.RequestReachable binary prime primePlan repr shape setup requestOf prior outside (requestOf earlier.1) →
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).1.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).1) ∧
      (BackendRuntimeContext.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf original remaining H coins earlier labels).2.Satisfies
        (Backend.logical (BackendRuntimeContext.cells binary prime primePlan binaryNodes repr shape setup requestOf original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (realFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw original remaining large contains)
      (simulateFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large contains) := by
  have nonnegative := Error.nonnegative (Fintype.card Digest) (Fintype.card Digest) 2 2443 84 preM postM 0
  simp only [Error.bound,Nat.cast_zero,zero_div,add_zero] at nonnegative
  have localLaw := mixed_hiding binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after outside draw original remaining pivotOne validHash satisfied
  have lifted := SHAGlobalWindow.restriction_statClose
    (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside) large contains nonnegative
    (fun coins table => realLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside draw original remaining (coins,table))
    (fun coins table => simulateLocal binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      requestOf prior after outside draw (coins,table)) localLaw
  unfold realFinite simulateFinite restrict restrictTable
  exact Probability.changeFintype lifted

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
