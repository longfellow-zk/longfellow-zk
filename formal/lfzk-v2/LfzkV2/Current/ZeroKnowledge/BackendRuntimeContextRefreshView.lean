import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext
import LfzkV2.Current.ZeroKnowledge.OracleHonestCoins
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshGames
import LfzkV2.Current.ZeroKnowledge.RequestedContextExperiment

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

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def refreshBefore
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) :=
  Observer.fixMerkle (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) prior

def refreshObserve
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (earlier : Prefix) (proof : Option Output) (H : Point → Digest × C) :
    Observer.View Bytes Digest Point (Digest × C) Context (Option Output) Observed :=
  let later := Observer.run (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) H (after earlier.1 proof)
  ⟨earlier.1,proof,earlier.2,later.1,later.2⟩

def programmedView (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (coin : (Fin 361 → B) × ((Point → Digest × C) × (Digest × C))) :=
  OracleHonestRefresh.programmed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) draw (requestOf ∘ Prod.fst)
    (refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM)
    (refreshObserve binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) coin

def honestView (frame : OracleHonestCoins.Frame binary prime binaryNodes)
    (HM : {raw // raw ∈ window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest)
    (coin : (Fin 361 → B) × ((Point → Digest × C) × (Digest × C))) :=
  OracleHonestRefresh.honest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining (OracleHonestCoins.assemble binary prime binaryNodes frame 0)
    (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) draw (requestOf ∘ Prod.fst)
    (refreshBefore binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM)
    (refreshObserve binary prime primePlan binaryNodes repr shape setup cfg prior after outside HM) coin


end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextReal
