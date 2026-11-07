import LfzkV2.Current.ZeroKnowledge.OracleNormalization
import LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdocRecording

/-! The honest frontend reads only canonical transcript coordinates.
The support statement follows from its actual recorded query history and
the existing ordinary trusted-circuit witness relation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestNormalization
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)

variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
local notation "baseAt" => OracleHonestCanonical.writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
local notation "rootAt" => OracleHonestCanonical.root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM
local notation "current" => OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H
local notation "samplers" => CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg
local notation "binaryRequest" => CanonicalRuntime.binaryRequest binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
  (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount

include bodyFits in
theorem queryLog_canonical (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan samplers (baseAt sample) H
      (FingerprintPrefix.context request (rootAt sample)) original responses coin converted)
    (point : Point) (member : point ∈ HonestTranscript.queryLog (current sample).state) :
    QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic point := by
  have inside : (current sample).state.rank.val < (G).roles.length := by
    rw [OracleHonestCanonical.result_rank]
    exact (G).batchingIndex.isLt
  let query := CompleteTranscript.query (Authentication := OpeningBody.Authentication G) (baseAt sample) (current sample).state inside
  have eqQuery := OracleHonestCanonical.batching_query binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM H sample pivotOne hash
  have encoded : QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic
      (CompleteCanonicalVerifier.batchingPoint binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request
        (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body H) := by
    unfold CompleteCanonicalVerifier.batchingPoint
    rw [BackendPath.parent_point]
    exact OracleBytes.replay_canonical repr shape setup binary.description.nPublic binaryRequest metadata bodyFits request cfg.initialLink
      (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample)
      H (G).batchingIndex.val (Nat.le_of_lt (G).batchingIndex.isLt)
  have canonical : QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic query :=
    (congrArg (QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic) eqQuery).mpr encoded
  obtain ⟨i,same⟩ := HonestTranscript.queryLog_mem_prior (Authentication := OpeningBody.Authentication G) (baseAt sample) (current sample).state inside point member
  exact (congrArg (QueryRuntime.Runtime.Canonical repr shape setup binary.description.nPublic) same).mpr
    (OracleCanonicalAncestors.canonical_priorPoints repr shape setup binary.description.nPublic query canonical i)

include bodyFits in
theorem frontend_eq (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan samplers (baseAt sample) H
      (FingerprintPrefix.context request (rootAt sample)) original responses coin converted)
    (agree : OracleNormalization.Agree repr shape setup binary.description.nPublic H H') :
    current sample = OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H' sample := by
  have run := HonestTranscript.Mdoc.program_congr_queryLog binary prime primePlan samplers (baseAt sample)
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request (rootAt sample)) original remaining tape.frontend tape.selectors H H'
    (fun point member => (agree point (queryLog_canonical binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape request HM H bodyFits sample pivotOne hash point member)).symm)
  have same := congrArg Prod.fst run
  rw [HonestTranscript.Mdoc.program_output,HonestTranscript.Mdoc.program_output] at same
  exact same.symm

end LfzkV2.Current.ZeroKnowledge.OracleHonestNormalization
