import LfzkV2.Current.ZeroKnowledge.OracleHonestTree
import LfzkV2.Current.ZeroKnowledge.OracleRefreshCompose

/-! The actual bounded honest program's active opening input has the
primary-mask freshness bound. Abort branches are excluded by the real
parser, and every successful key is the literal canonical proof preimage. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestTree
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1600000
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

theorem active_output (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted) :
    active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ↔
    OracleHonestRuntime.active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H sample := by
  unfold active
  rw [pending_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM draw H sample pivotOne hash]
  unfold OracleHonestRuntime.pending OracleHonestRuntime.active
  cases parsed : OracleHonestRuntime.statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H sample <;> rfl

theorem pending_key (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted)
    (proof : Output)
    (existsProof : OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H draw sample = some proof) :
    input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 =
    ((CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request).encoding.chain cfg.initialLink).point proof H (G).openingIndex.val := by
  have actual := (pending_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM draw H sample pivotOne hash).trans existsProof
  unfold asPending at actual
  cases parsed : parse binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.frontend with
  | none =>
    simp only [parsed,Option.bind_eq_bind,Option.bind_none] at actual
    cases actual
  | some data =>
    simp only [parsed,Option.bind_eq_bind,Option.bind_some,Option.pure_def] at actual
    have same := Option.some.inj actual
    have key := input_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM draw H sample pivotOne hash
    exact key.trans (congrArg (fun out : Output =>
      ((CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request).encoding.chain cfg.initialLink).point out H (G).openingIndex.val) same)

variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)

/-- The physical opening preimage produced by the honest causal program. -/
def boundaryBytes (sample : Fin 361 → B) : Bytes :=
  QueryRuntime.Runtime.pointBytes (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    repr shape setup binary.description.nPublic fits
    (input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1)

theorem input_active (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted)
    (enabled : active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1) :
    boundaryBytes binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H fits sample =
      OracleHonestRuntime.input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM H draw fits sample := by
  have enabled' := enabled
  unfold active at enabled'
  rw [pending_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM draw H sample pivotOne hash] at enabled'
  cases parsed : OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H draw sample with
  | none => simp only [parsed,Option.isSome_none,Bool.false_eq_true] at enabled'
  | some proof =>
    have key := pending_key binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM draw H sample pivotOne hash proof parsed
    unfold OracleHonestRuntime.input
    rw [parsed]
    exact congrArg (QueryRuntime.Runtime.pointBytes (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) repr shape setup binary.description.nPublic fits) key

variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)

include bodyFits in
theorem active_input_queries (pivotOne : binary.basis 0 = 1)
    (hash : ∀ sample responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted)
    (prior : Finset Bytes) (queries : ℕ) (budget : prior.card ≤ queries) :
    ((Finset.univ.filter fun sample : Fin 361 → B =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∧
      boundaryBytes binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H fits sample ∈ prior).card : ℚ) /
      (2 : ℚ)^46208 ≤ (queries : ℚ)/(2 : ℚ)^46208 := by
  have contained : (Finset.univ.filter fun sample : Fin 361 → B =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∧
      boundaryBytes binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H fits sample ∈ prior) ⊆
      (Finset.univ.filter fun sample : Fin 361 → B =>
        OracleHonestRuntime.active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample ∧
        OracleHonestRuntime.input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw fits sample ∈ prior) := by
    intro sample member
    obtain ⟨_,enabled,member⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (active_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM draw H sample pivotOne (hash sample)).mp enabled,
      (input_active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM draw H fits sample pivotOne (hash sample) enabled) ▸ member⟩
  refine le_trans ?_ (OracleHonestRuntime.active_queries binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM H draw fits bodyFits prior queries budget)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card contained

omit [DecidableEq B] in
include binary in
theorem primary_mask_card : Fintype.card (Fin 361 → B) = 2^46208 := by
  rw [Fintype.card_fun,Fintype.card_fin,OracleJointPrimaryFreshness.binary_card binary,←pow_mul]

include fits bodyFits in
theorem active_point_queries (pivotOne : binary.basis 0 = 1)
    (hash : ∀ sample responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted)
    (prior : Finset Point) (queries : ℕ) (budget : prior.card ≤ queries) :
    ((Finset.univ.filter fun sample : Fin 361 → B =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∧
      input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∈ prior).card : ℚ) /
      Fintype.card (Fin 361 → B) ≤ (queries : ℚ)/(2 : ℚ)^46208 := by
  let raw := prior.image (QueryRuntime.Runtime.pointBytes (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) repr shape setup binary.description.nPublic fits)
  have rawBudget : raw.card ≤ queries := (Finset.card_image_le).trans budget
  have bound := active_input_queries binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM draw H fits bodyFits pivotOne hash raw queries rawBudget
  have contained : (Finset.univ.filter fun sample : Fin 361 → B =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∧
      input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∈ prior) ⊆
      (Finset.univ.filter fun sample : Fin 361 → B =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
        ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 ∧
      boundaryBytes binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H fits sample ∈ raw) := by
    intro sample member
    obtain ⟨_,enabled,member⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,enabled,Finset.mem_image_of_mem _ member⟩
  rw [primary_mask_card binary]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  refine le_trans ?_ bound
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card contained

end LfzkV2.Current.ZeroKnowledge.OracleHonestTree
