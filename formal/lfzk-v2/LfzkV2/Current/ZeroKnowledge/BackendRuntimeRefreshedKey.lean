import LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal

/-! The source opening query is the canonical pending-proof key. Keep this
readback at the single-circuit boundary, before a public request selects
its circuit values and private observation state. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxRecDepth 4096

variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
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
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

local notation "rootAt" => OracleHonestCanonical.root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM
local notation "baseAt" => OracleHonestCanonical.writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
local notation "samplers" => CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg

variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)

theorem pending_refreshed_key (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted)
    (proof : Output)
    (parsed : OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H draw sample = some proof) :
    OracleHonestTree.input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
        ((OracleHonestTree.tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
          original remaining tape request HM draw sample).run H).1 =
      refreshedKey binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request H proof := by
  unfold refreshedKey
  exact OracleHonestTree.pending_key binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM draw H sample pivotOne hash proof parsed

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal
