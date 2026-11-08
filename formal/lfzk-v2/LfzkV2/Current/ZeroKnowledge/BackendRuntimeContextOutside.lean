import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext
import LfzkV2.Current.ZeroKnowledge.SHAComplement

/-! Stateful finite backend games depend on the complementary SHA values
only through the filtered observer trees. Equal complementary slices give
identical games after transporting the same raw-valued finite table. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextOutside
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

omit [DecidableEq Observed] in
theorem window_eq (first second : Bytes → Digest)
    (agree : ∀ raw, ¬SHAOracle.merkleDomain raw → first raw = second raw) :
    BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after first =
      BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after second := by
  unfold BackendRuntimeContext.window BackendRuntimeContext.trees
  exact congrArg (BackendRuntime.windowContextForTrees binary prime primePlan binaryNodes repr shape setup cfg)
    (SHAComplement.trees_eq SHAOracle.merkleDomain first second agree prior after)

omit [DecidableEq Observed] in
theorem real_heq (first second : Bytes → Digest)
    (agree : ∀ raw, ¬SHAOracle.merkleDomain raw → first raw = second raw)
    (H : Point → Digest × C) (answer : Digest × C) :
    HEq
      (BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after first draw original remaining H answer)
      (BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after second draw original remaining H answer) := by
  unfold BackendRuntimeContext.real BackendRuntimeContext.trees
  exact congr_arg_heq (BackendRuntime.realContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining H draw answer requestOf) (SHAComplement.trees_eq SHAOracle.merkleDomain first second agree prior after)

omit [DecidableEq Observed] in
theorem simulatedPublic_heq (first second : Bytes → Digest)
    (agree : ∀ raw, ¬SHAOracle.merkleDomain raw → first raw = second raw)
    (H : Point → Digest × C) (answer : Digest × C) :
    HEq
      (BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after first draw H answer)
      (BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after second draw H answer) := by
  unfold BackendRuntimeContext.simulatedPublic BackendRuntimeContext.trees
  exact congr_arg_heq (BackendRuntime.simulatedPublicContextForTrees binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    H draw answer requestOf) (SHAComplement.trees_eq SHAOracle.merkleDomain first second agree prior after)

private theorem coin_heq {Raw Value Outer Rest : Type} (first second : Finset Raw) (same : first = second)
    (H : Raw → Value) (outer : Outer) (rest : Rest) :
    HEq (outer,((fun raw : {raw // raw ∈ first} => H raw.val),rest))
      (outer,((fun raw : {raw // raw ∈ second} => H raw.val),rest)) := by
  cases same
  rfl

omit [DecidableEq Observed] in
theorem real_at (first second : Bytes → Digest)
    (agree : ∀ raw, ¬SHAOracle.merkleDomain raw → first raw = second raw)
    (HM : Bytes → Digest) (H : Point → Digest × C) (answer : Digest × C)
    (frontend : FrontCoins)
    (backend : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells (CellLayout.Prime.cells prime.remaining prime.pads))
    (nonces : Fin 2443 → MerkleNonce) (labels : Fin (2*2443-1) → Digest) :
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after first draw original remaining H answer
      ((frontend,backend),((fun raw => HM raw.val),(nonces,labels))) =
    BackendRuntimeContext.real binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after second draw original remaining H answer
      ((frontend,backend),((fun raw => HM raw.val),(nonces,labels))) := by
  have functions := real_heq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after draw original remaining first second agree H answer
  have arguments := coin_heq
    (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after first)
    (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after second)
    (window_eq binary prime primePlan binaryNodes repr shape setup cfg prior after first second agree) HM (frontend,backend) (nonces,labels)
  exact congr_heq functions arguments

omit [DecidableEq Observed] in
theorem simulatedPublic_at (first second : Bytes → Digest)
    (agree : ∀ raw, ¬SHAOracle.merkleDomain raw → first raw = second raw)
    (HM : Bytes → Digest) (H : Point → Digest × C) (answer : Digest × C)
    (frontend : CompleteSimulation.Coins binary prime)
    (backend : CompleteBackend.Masks binaryNodes ConcreteSetup.primeNodes binary.description.cells (CellLayout.Prime.cells prime.remaining prime.pads))
    (nonces : Fin 2443 → MerkleNonce) (labels : Fin (2*2443-1) → Digest) :
    BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after first draw H answer
      ((frontend,backend),((fun raw => HM raw.val),(nonces,labels))) =
    BackendRuntimeContext.simulatedPublic binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after second draw H answer
      ((frontend,backend),((fun raw => HM raw.val),(nonces,labels))) := by
  have functions := simulatedPublic_heq binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata requestOf prior after draw first second agree H answer
  have arguments := coin_heq
    (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after first)
    (BackendRuntimeContext.window binary prime primePlan binaryNodes repr shape setup cfg prior after second)
    (window_eq binary prime primePlan binaryNodes repr shape setup cfg prior after first second agree) HM (frontend,backend) (nonces,labels)
  exact congr_heq functions arguments

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeContextOutside
