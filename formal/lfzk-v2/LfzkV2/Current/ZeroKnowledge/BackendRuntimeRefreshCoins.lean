import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRegroup
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRealCoins

/-! Regroup the honest source coins so the complete opening-refresh law
can be averaged at each fixed frame and finite Merkle table. Unused labels
remain explicit independent coins; no oracle output is added to the view. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeRefreshCoins
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate
attribute [local irreducible] BackendRuntime.real RequestedExperiment.simulated
attribute [local irreducible] StatClose probOf

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
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape

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
  BackendRuntime.frontCoinsFintype BackendRuntime.genericBackendMasksFintype
  BackendRuntime.backendMasksFintype BackendRuntime.merkleCoinsFintype BackendRuntime.coinsFintype

abbrev Outer := OracleHonestCoins.Frame binary prime binaryNodes ×
  (({raw // raw ∈ BackendRuntime.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest) ×
    (Fin (2*2443-1) → Digest))

abbrev Challenges := (Fin 361 → B) × BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup

private def order {OracleSpace FrameSpace MaskSpace OtherSpace : Type} :
    (OracleSpace × ((FrameSpace × MaskSpace) × OtherSpace)) ≃
      ((FrameSpace × OtherSpace) × (MaskSpace × OracleSpace)) where
  toFun coin := ((coin.2.1.1,coin.2.2),(coin.2.1.2,coin.1))
  invFun coin := (coin.2.2,((coin.1.1,coin.2.1),coin.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Split only independent private coins. The primary-mask evaluations are
uniform because the existing interpolation map is a field-linear equivalence;
no transcript, root or selected request is conditioned on here. -/
def split : BackendRuntimeMixed.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    (Outer binary prime primePlan binaryNodes repr shape setup cfg prior after outside ×
      Challenges (C := C) binary prime primePlan repr shape setup) :=
  ((Equiv.prodCongr (Equiv.refl _) (BackendRuntimeReal.privateCoinEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside)).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (OracleHonestCoins.equivalence binary prime binaryNodes).symm (Equiv.refl _)))).trans order

omit [DecidableEq Observed] in
theorem split_symm (outer : Outer binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    (challenges : Challenges (C := C) binary prime primePlan repr shape setup) :
    (split binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm (outer,challenges) =
      (challenges.2,BackendRuntimeReal.privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside
        (OracleHonestCoins.assemble binary prime binaryNodes outer.1 challenges.1) outer.2.1 outer.2.2) := rfl

/-- The same private coins with the finite Merkle table placed last for
subsequent averaging over the shared raw SHA oracle. -/
def tableEquiv :
    (Outer binary prime primePlan binaryNodes repr shape setup cfg prior after outside ×
      Challenges (C := C) binary prime primePlan repr shape setup) ≃
    (BackendRuntimeRegroup.PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
      BackendRuntimeRegroup.Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  (split binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm.trans
    (BackendRuntimeRegroup.privateEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside)

omit [DecidableEq Observed] in
theorem tableEquiv_apply (outer : Outer binary prime primePlan binaryNodes repr shape setup cfg prior after outside)
    (challenges : Challenges (C := C) binary prime primePlan repr shape setup) :
    tableEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside (outer,challenges) =
      BackendRuntimeRegroup.privateEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside
        (challenges.2,BackendRuntimeReal.privateCoin binary prime primePlan binaryNodes repr shape setup cfg prior after outside
          (OracleHonestCoins.assemble binary prime binaryNodes outer.1 challenges.1) outer.2.1 outer.2.2) := rfl

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeRefreshCoins
