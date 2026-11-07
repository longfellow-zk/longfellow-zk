import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
import LfzkV2.Current.ZeroKnowledge.OracleHonestCoins

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeContext BackendRuntimeContextEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run

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
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

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

def privateCoin (tape : HonestRuntime.Tape binary prime binaryNodes)
    (HM : {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (labels : Fin (2*2443-1) → Digest) :
    BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside :=
  (((tape.frontend,tape.selectors),tape.backend),(HM,tape.nonces,labels))

omit [DecidableEq Observed] in
theorem honestTape_privateCoin (tape : HonestRuntime.Tape binary prime binaryNodes)
    (HM : {raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (labels : Fin (2*2443-1) → Digest) :
    honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside
        (privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside tape HM labels) = tape := rfl

def privateCoinEquiv : BackendRuntimeContext.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    HonestRuntime.Tape binary prime binaryNodes ×
      (({raw // raw ∈ BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) ×
        (Fin (2*2443-1) → Digest)) where
  toFun coin := (honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin,(coin.2.1,coin.2.2.2))
  invFun coin := privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.1 coin.2.1 coin.2.2
  left_inv coin := by rfl
  right_inv coin := by
    rcases coin with ⟨⟨frontend,selectors,backend,nonces⟩,HM,labels⟩
    rfl

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
