import LfzkV2.Current.ZeroKnowledge.BackendRuntimeMixed

/-! Put the finite Merkle table last in the complete simulation experiment.
The remaining coins do not depend on the table's finite byte window or its
fixed complementary oracle. This is only a bijective regrouping of independent
coins, so later finite-window averaging changes no probability or query budget. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeRegroup
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate
attribute [local irreducible] BackendRuntime.real RequestedExperiment.simulated
attribute [local irreducible] StatClose probOf

/-- After the Merkle marginal has been lifted to a fixed global window,
put the transcript table last for the raw transcript-oracle marginal. This
is a pure permutation: the answer and all other private coins remain fixed. -/
def transcriptLast {Transcript Answer Private TableSpace : Type} :
    (((Transcript × Answer) × Private) × TableSpace) ≃
      (((Answer × Private) × TableSpace) × Transcript) where
  toFun coin := (((coin.1.1.2,coin.1.2),coin.2),coin.1.1.1)
  invFun coin := (((coin.2,coin.1.1.1),coin.1.1.2),coin.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

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

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)

abbrev PrivateOuter := BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup ×
  ((CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) ×
    CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) ×
  HidingSample 2443 (2*2443-1) MerkleNonce Digest

abbrev PublicOuter := BackendRuntimeMixed.OracleCoins (C := C) binary prime primePlan repr shape setup ×
  (CompleteSimulation.Coins binary prime ×
    CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells
      (CellLayout.Prime.cells prime.remaining prime.pads)) ×
  HidingSample 2443 (2*2443-1) MerkleNonce Digest

abbrev Table := {raw // raw ∈ BackendRuntime.window binary prime primePlan binaryNodes repr shape setup cfg prior after outside} → Digest

private def tableLast {OracleSpace OuterSpace TableSpace RestSpace : Type} :
    (OracleSpace × (OuterSpace × (TableSpace × RestSpace))) ≃
      ((OracleSpace × OuterSpace × RestSpace) × TableSpace) where
  toFun coin := ((coin.1,coin.2.1,coin.2.2.2),coin.2.2.1)
  invFun coin := (coin.1.1,(coin.1.2.1,coin.2,coin.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def privateEquiv : BackendRuntimeMixed.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    (PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
      Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) := tableLast

def publicEquiv : BackendRuntimeMixed.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside ≃
    (PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
      Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) := tableLast

@[irreducible] def real (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  BackendRuntimeMixed.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    draw original remaining ((privateEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm coin)

@[irreducible] def simulate (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  BackendRuntimeMixed.simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    draw ((publicEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm coin)

omit [DecidableEq Observed] in
theorem real_apply (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining coin =
      BackendRuntimeMixed.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        draw original remaining ((privateEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm coin) := by
  unfold real
  rfl

omit [DecidableEq Observed] in
theorem simulate_apply (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw coin =
      BackendRuntimeMixed.simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        draw ((publicEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm coin) := by
  unfold simulate
  rfl

omit [DecidableEq Observed] in
theorem real_literal (coin : PrivateOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining coin =
      BackendRuntime.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining coin.1.1.1 draw coin.1.1.2
        (coin.1.2.1,(coin.2,coin.1.2.2)) := by
  rw [real_apply,BackendRuntimeMixed.real_pair,BackendRuntimeMixed.realAt_apply]
  rfl

omit [DecidableEq Observed] in
theorem simulate_literal (coin : PublicOuter (C := C) binary prime primePlan binaryNodes repr shape setup ×
    Table binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw coin =
      RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw prior after
        (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.1.1.2
          (coin.1.2.1,(coin.2,coin.1.2.2)))
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2) coin.1.1.1 := by
  rw [simulate_apply,BackendRuntimeMixed.simulate_pair,BackendRuntimeMixed.simulateAt_apply]
  rfl

variable (pivotOne : binary.basis 0 = 1)
variable (validHash : ∀ (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) earlier labels,
  BackendRuntime.hashChecks binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original H earlier labels)

include pivotOne validHash in
omit [DecidableEq Observed] in
theorem statClose
    (satisfied : ∀ (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) coins earlier labels,
      (BackendRuntime.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins earlier labels).1.Satisfies (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coins earlier).1) ∧
      (BackendRuntime.statements binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
        coins earlier labels).2.Satisfies (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coins earlier).2)) :
    StatClose (2*MerklePreparation.error (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card MerkleNonce) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining)
      (simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw) := by
  have mixed := BackendRuntimeMixed.statClose binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    prior after outside draw original remaining pivotOne validHash satisfied
  exact Probability.changeFintype (statClose_reindex
    (privateEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm
    (publicEquiv binary prime primePlan binaryNodes repr shape setup cfg prior after outside).symm
    (real_apply binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining)
    (simulate_apply binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw) mixed)

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeRegroup
