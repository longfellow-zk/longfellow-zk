import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextOutside
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextSimulator

/-! The enlarged-table simulator endpoint is the literal complete
stateful simulator at that one full SHA oracle. No unqueried coordinate
is discarded or replaced in the actual final experiment. -/
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

private theorem extend_self {Raw Value : Type} [DecidableEq Raw]
    (window : Finset Raw) (H : Raw → Value) : OracleWindow.extend window (fun raw => H raw.val) H = H := by
  funext raw
  unfold OracleWindow.extend
  split <;> rfl

omit [DecidableEq Observed] in
theorem expanded_self (HM : Bytes → Digest) :
    BackendRuntimeContext.expanded binary prime primePlan binaryNodes repr shape setup cfg prior after HM
      (fun raw => HM raw.val) = HM :=
  extend_self (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after HM) HM

variable (large : Finset Bytes)
variable (contains : BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside ⊆ large)
variable (onlyMerkle : ∀ raw ∈ large, SHAOracle.merkleDomain raw)

include onlyMerkle in
omit [DecidableEq Observed] in
theorem simulator_global (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup × Table large) :
    simulateFinite binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large contains coin =
      simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after outside draw large
        (BackendRuntimeGlobalCoins.publicTranscriptEquiv binary prime primePlan binaryNodes repr shape setup (Table large) coin) := by
  let HM := oracle outside large coin.2
  let H := coin.1.1.1
  let answer := coin.1.1.2
  let localCoin : BackendRuntimeContext.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after HM :=
    (coin.1.2.1,((fun raw => HM raw.val),coin.1.2.2))
  have agree : ∀ raw, ¬SHAOracle.merkleDomain raw → outside raw = HM raw := by
    intro raw off
    exact (oracle_complement outside large onlyMerkle coin.2 raw off).symm
  have transported := BackendRuntimeContextOutside.simulatedPublic_at binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after draw outside HM agree HM H answer coin.1.2.1.1 coin.1.2.1.2 coin.1.2.2.1 coin.1.2.2.2
  have endpoint := BackendRuntimeContextSimulator.simulatedPublic_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    requestOf prior after HM draw H answer localCoin
  rw [expanded_self] at endpoint
  unfold simulateFinite simulateLocal simulate
  rw [restrict_oracle]
  exact transported.trans endpoint

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextGlobal
