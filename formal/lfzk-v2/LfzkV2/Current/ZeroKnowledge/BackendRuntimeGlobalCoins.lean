import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRefreshCoins

/-! Coin layouts shared by the fixed global SHA and raw transcript-oracle
marginals. All prover coin spaces are independent of either observer syntax
or oracle complements; an arbitrary finite table is a separate factor. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeGlobalCoins
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

abbrev PrivateRest :=
  ((CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) ×
    CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) × HidingSample 2443 (2*2443-1) MerkleNonce Digest

abbrev PublicRest :=
  (CompleteSimulation.Coins binary prime ×
    CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) × HidingSample 2443 (2*2443-1) MerkleNonce Digest

abbrev PrivateProver := (Digest × C) × PrivateRest binary prime binaryNodes
abbrev PublicProver := (Digest × C) × PublicRest binary prime binaryNodes
abbrev Frame := OracleHonestCoins.Frame binary prime binaryNodes × (Fin (2*2443-1) → Digest)

/-- The actual honest private tape and an independent unused label tape. -/
def sourceEquiv : PrivateRest binary prime binaryNodes ≃
    (HonestRuntime.Tape binary prime binaryNodes × (Fin (2*2443-1) → Digest)) where
  toFun coin := (⟨coin.1.1.1,coin.1.1.2,coin.1.2,coin.2.1⟩,coin.2.2)
  invFun coin := (((coin.1.frontend,coin.1.selectors),coin.1.backend),coin.1.nonces,coin.2)
  left_inv _ := rfl
  right_inv coin := by
    rcases coin with ⟨⟨frontend,selectors,backend,nonces⟩,labels⟩
    rfl

private def frameOrder {OracleSpace FrameSpace MaskSpace OtherSpace : Type} :
    (OracleSpace × ((FrameSpace × MaskSpace) × OtherSpace)) ≃
      ((FrameSpace × OtherSpace) × (MaskSpace × OracleSpace)) where
  toFun coin := ((coin.2.1.1,coin.2.2),(coin.2.1.2,coin.1))
  invFun coin := (coin.2.2,((coin.1.1,coin.2.1),coin.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- This equivalence does not mention the Merkle query window or its
complement. Only independent source coins and the primary interpolation
map are rearranged. -/
def outerEquiv : BackendRuntimeRegroup.PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ≃
    (Frame binary prime binaryNodes × BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :=
  ((Equiv.prodCongr (Equiv.refl _) (sourceEquiv binary prime binaryNodes)).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (OracleHonestCoins.equivalence binary prime binaryNodes).symm (Equiv.refl _)))).trans frameOrder

private def tableOrder {FrameSpace ChallengeSpace TableSpace : Type} :
    ((FrameSpace × ChallengeSpace) × TableSpace) ≃ ((FrameSpace × TableSpace) × ChallengeSpace) where
  toFun coin := ((coin.1.1,coin.2),coin.1.2)
  invFun coin := ((coin.1.1,coin.2),coin.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

def refreshEquiv (TableSpace : Type) :
    (BackendRuntimeRegroup.PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × TableSpace) ≃
    ((Frame binary prime binaryNodes × TableSpace) ×
      BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :=
  (Equiv.prodCongr (outerEquiv binary prime primePlan binaryNodes repr shape setup) (Equiv.refl _)).trans tableOrder

omit [Fintype B] [Fintype C] [DecidableEq Observed] in
theorem refreshEquiv_symm {TableSpace : Type}
    (frame : Frame binary prime binaryNodes) (table : TableSpace)
    (challenges : BackendRuntimeRefreshCoins.Challenges (C := C) binary prime primePlan repr shape setup) :
    (refreshEquiv binary prime primePlan binaryNodes repr shape setup TableSpace).symm ((frame,table),challenges) =
      ((challenges.2,(sourceEquiv binary prime binaryNodes).symm
        (OracleHonestCoins.assemble binary prime binaryNodes frame.1 challenges.1,frame.2)),table) := rfl

def privateTranscriptEquiv (TableSpace : Type) :
    (BackendRuntimeRegroup.PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup × TableSpace) ≃
    ((PrivateProver (C := C) binary prime binaryNodes × TableSpace) ×
      (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)) :=
  BackendRuntimeRegroup.transcriptLast

def publicTranscriptEquiv (TableSpace : Type) :
    (BackendRuntimeRegroup.PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup × TableSpace) ≃
    ((PublicProver (C := C) binary prime binaryNodes × TableSpace) ×
      (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)) :=
  BackendRuntimeRegroup.transcriptLast

def honestTape {TableSpace : Type} (coin : PrivateProver (C := C) binary prime binaryNodes × TableSpace) :
    HonestRuntime.Tape binary prime binaryNodes := (sourceEquiv binary prime binaryNodes coin.1.2).1

def simulatorTape {TableSpace : Type} (coin : PublicProver (C := C) binary prime binaryNodes × TableSpace) :
    CompleteSimulator.Tape (C := C) binary prime binaryNodes where
  frontend := coin.1.2.1.1
  backend := coin.1.2.1.2
  nonces := coin.1.2.2.1
  answer := coin.1.1

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeGlobalCoins
