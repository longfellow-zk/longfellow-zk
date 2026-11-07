import LfzkV2.Current.ZeroKnowledge.BackendRuntimeSimulator
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Average the backend/frontend simulation over one independent complete
transcript table and one complete opening answer. The observer always receives
the table returned by the actual simulator; no conditioning on that table is
used to assert independence of its source coins. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeMixed
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run CompleteSimulation.simulate
attribute [local irreducible] BackendRuntime.real RequestedExperiment.simulated
attribute [local irreducible] StatClose probOf

private theorem error_nonnegative (salts digests columns openings earlier later : ℕ) :
    0 ≤ 2*MerklePreparation.error salts digests columns earlier +
      MerkleSimulation.openingError salts digests columns (columns-openings) later := by
  unfold MerklePreparation.error MerkleSimulation.openingError
  positivity

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

abbrev OracleCoins := (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C) × (Digest × C)
abbrev PrivateCoins := OracleCoins (C := C) binary prime primePlan repr shape setup ×
  BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside
abbrev PublicCoins := OracleCoins (C := C) binary prime primePlan repr shape setup ×
  BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside

/-- Conditioned views keep both oracle answers fixed while the independent
backend/frontend coins vary. The product experiment only regroups those same
coins; it does not expose or resample a resulting programmed table. -/
@[irreducible] def realAt (oracle : OracleCoins (C := C) binary prime primePlan repr shape setup)
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  BackendRuntime.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
    original remaining oracle.1 draw oracle.2 coin

@[irreducible] def simulateAt (oracle : OracleCoins (C := C) binary prime primePlan repr shape setup)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
    prior after (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside oracle.2 coin)
    (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) oracle.1

@[irreducible] def real (coin : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  realAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining coin.1 coin.2

@[irreducible] def simulate (coin : PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  simulateAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw coin.1 coin.2

omit [DecidableEq Observed] in
theorem realAt_apply (oracle : OracleCoins (C := C) binary prime primePlan repr shape setup)
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    realAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining oracle coin =
      BackendRuntime.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside
        original remaining oracle.1 draw oracle.2 coin := by
  unfold realAt
  rfl

omit [DecidableEq Observed] in
theorem simulateAt_apply (oracle : OracleCoins (C := C) binary prime primePlan repr shape setup)
    (coin : BackendRuntime.PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulateAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw oracle coin =
      RequestedExperiment.simulated binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw prior after
        (simulatorTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside oracle.2 coin)
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1) oracle.1 := by
  unfold simulateAt
  rfl

omit [DecidableEq Observed] in
theorem real_pair (coin : PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining coin =
      realAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining coin.1 coin.2 := by
  unfold real
  rfl

omit [DecidableEq Observed] in
theorem simulate_pair (coin : PublicCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw coin =
      simulateAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw coin.1 coin.2 := by
  unfold simulate
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
    StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
      MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
      (real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining)
      (simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw) := by
  have nonnegative := error_nonnegative (Fintype.card Digest) (Fintype.card Digest) 2443 84 preM postM
  have each (oracle : OracleCoins (C := C) binary prime primePlan repr shape setup) :
      StatClose (2*MerklePreparation.error (Fintype.card Digest) (Fintype.card Digest) 2443 preM +
        MerkleSimulation.openingError (Fintype.card Digest) (Fintype.card Digest) 2443 (2443-84) postM)
        (realAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining oracle)
        (simulateAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw oracle) := by
    unfold realAt simulateAt
    exact Probability.changeFintype (BackendRuntimeSimulator.simulator_statClose binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      prior after outside draw original remaining oracle.1 pivotOne (validHash oracle.1) oracle.2 (satisfied oracle.1))
  have mixed := statClose_mix nonnegative
    (realAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw original remaining)
    (simulateAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata prior after outside draw) each
  unfold real simulate
  exact Probability.changeFintype mixed

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeMixed
