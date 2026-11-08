import LfzkV2.Current.ZeroKnowledge.OracleResponseSamples

/-! Raw prequery counting for the actual joint honest H/Z constructor.
The frontend (and its commitment) may depend arbitrarily on the binary
primary mask. Both complete responses are produced by the runtime encoder;
their batching coin is obtained from the canonical strict earlier prefix.
An arbitrary malformed prior byte string can match at most one fresh mask. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleJointPrimaryFreshness
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend Polynomial
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
local notation "Mask" => Fin 361 → B

variable (binaryRequest : (Fin binary.description.nPublic → Bool) → Fin shape.binaryPublic → B)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
variable (request : CanonicalRequest.Request shape binary.description.nPublic)
variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg)
local notation "E" => CanonicalRequest.encoding repr shape setup binary.description.nPublic binaryRequest metadata request

variable (logical : Backend.Cells B (ConcreteSetup.rows binary.description.cells) 265 ×
  Backend.Cells N (ConcreteSetup.rows (CellLayout.Prime.cells prime.remaining prime.pads)) 265)
variable (core : PolygeroCoreMasking.Tape B 84 (ConcreteSetup.rows binary.description.cells) 0)
variable (masks : PolygeroMasking.Tape (Backend.profileGeometry binaryNodes).code (PolygeroZk.sumFunctional B 265))
variable (primeTape : Backend.ProfileTape primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
variable (frontend : (Fin 361 → B) → CanonicalRequest.Output
  (g := CompleteSimulation.geometry binary prime primePlan) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))
variable (statement : (Fin 361 → B) → JointResponse.Statement
  (RuntimeVerifier.first binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
    (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).participant
  (RuntimeVerifier.second binary.description prime (ConcreteSetup.backend binaryNodes binary.description.cells)
    (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).participant)

def batching (sample : Mask) : Point := ((E).chain cfg.initialLink).point (frontend sample) H (G).batchingIndex.val

def coin (point : Point) := RuntimeVerifier.batchingDecoder binary.description prime P R cfg draw (H point).2

def response (sample : Mask) :=
  CompleteVerifier.wireResponses binary.description prime binaryNodes primeNodes cfg
    (CompleteResponse.realResponses binary.description prime binaryNodes primeNodes cfg logical (statement sample)
      (coin binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw
        (batching binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H frontend sample))
      ((core,masks,(Response.evaluationEquiv B (OraclePrimaryFreshness.nodes binaryNodes)
        (OraclePrimaryFreshness.nodes_injective binaryNodes)).symm sample),primeTape))

def proof (sample : Mask) : Output :=
  OracleResponse.proofBoth (frontend sample)
    (response binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement sample)

def historyOf (sample : Mask) : Point :=
  ((E).chain cfg.initialLink).point
    (proof binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement sample) H (G).openingIndex.val

def batchPart (point : Point) : Mask := fun i =>
  (PolygeroPrimaryMasking.batch (Backend.profileGeometry binaryNodes).positive
    (coin binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw point).1.2
    (PolygeroZk.ordinaryRows (Backend.profileGeometry binaryNodes) (Backend.messages logical.1) core masks)).val.eval
      (OraclePrimaryFreshness.nodes binaryNodes i)

def base (point : Point) : Mask :=
  match point.atRank (G).batchingIndex.val with
  | none => 0
  | some parent => batchPart binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks parent

theorem base_history (sample : Mask) :
    base binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks
      (historyOf binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement sample) =
      batchPart binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks
        (batching binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H frontend sample) := by
  unfold base historyOf
  rw [(E).point_atRank cfg.initialLink _ H (G).openingIndex.val (G).batchingIndex.val
    (Nat.le_of_lt (G).openingIndex.isLt) (by have := (G).openingIndex_val; omega)]
  rw [proof,OracleResponse.batchingBoth_point repr shape setup binary.description.nPublic binaryRequest metadata request]
  rfl

theorem primary_formula (sample : Mask) :
    (fun i : Fin 361 => cfg.binaryField
      ((response binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement sample).1.h i)) =
      sample + batchPart binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks
        (batching binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H frontend sample) := by
  exact OracleResponseSamples.real_binary_primary binary prime primePlan binaryNodes primeNodes cfg
    (OrderedOpening.query (cfg.sample (H (batching binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H frontend sample)).2))
    logical (statement sample)
    (coin binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw
      (batching binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H frontend sample))
    core masks primeTape sample

variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)

def input (sample : Mask) : Bytes :=
  OracleBytes.openingBytes repr shape setup binary.description.nPublic fits binaryRequest metadata request cfg.initialLink
    (proof binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement sample) H

def read (raw : Bytes) : Option (Point × Mask) :=
  (OracleBytes.taggedPrimary repr shape setup binary.description.nPublic fits .binary raw).map fun value =>
    (value.1,fun i : Fin 361 => cfg.binaryField (value.2 i))

include bodyFits in
theorem decoded_formula (sample : Mask) :
    read binary prime primePlan binaryNodes primeNodes repr shape setup cfg fits
      (input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample) =
      some (OpeningFreshness.taggedResponse
        (historyOf binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
          logical core masks primeTape frontend statement)
        (base binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks) sample) := by
  unfold read input
  rw [OracleBytes.opening_tagged_binary repr shape setup binary.description.nPublic fits binaryRequest metadata bodyFits]
  change some (_,fun i : Fin 361 => cfg.binaryField
    ((response binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement sample).1.h i)) = _
  rw [primary_formula,← base_history]
  rfl

include bodyFits in
theorem raw_hit_probability (prior : Finset Bytes) :
    ((Finset.univ.filter fun sample : Mask =>
      input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample ∈ prior).card : ℚ) /
      (Fintype.card B)^361 ≤ (prior.card : ℚ)/(Fintype.card B)^361 := by
  have bound := OracleBytes.raw_hit_probability
    (historyOf binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement)
    (base binary prime primePlan binaryNodes primeNodes repr shape setup cfg H draw logical core masks)
    (input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement fits)
    (read binary prime primePlan binaryNodes primeNodes repr shape setup cfg fits)
    (decoded_formula binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement fits bodyFits) prior
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using bound

include binary in
omit [DecidableEq B] in
theorem binary_card : Fintype.card B = 2^128 := by
  rw [Fintype.card_congr binary.basis.equivFun.toEquiv,Fintype.card_fun,Fintype.card_fin,ZMod.card]

include bodyFits in
theorem active_raw_hit_probability (active : (Fin 361 → B) → Prop) (prior : Finset Bytes) :
    ((Finset.univ.filter fun sample : Mask => active sample ∧
      input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample ∈ prior).card : ℚ) /
      (Fintype.card B)^361 ≤ (prior.card : ℚ)/(Fintype.card B)^361 := by
  have contained : (Finset.univ.filter fun sample : Mask => active sample ∧
      input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample ∈ prior) ⊆
      (Finset.univ.filter fun sample : Mask =>
        input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
          logical core masks primeTape frontend statement fits sample ∈ prior) := by
    intro sample member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp member).2.2⟩
  exact le_trans
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card contained)) (by positivity))
    (raw_hit_probability binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
      logical core masks primeTape frontend statement fits bodyFits prior)

include bodyFits in
theorem active_raw_queries (active : (Fin 361 → B) → Prop) (prior : Finset Bytes) (queries : ℕ)
    (budget : prior.card ≤ queries) :
    ((Finset.univ.filter fun sample : Mask => active sample ∧
      input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample ∈ prior).card : ℚ) /
      (2 : ℚ)^46208 ≤ (queries : ℚ)/(2 : ℚ)^46208 := by
  have bound := active_raw_hit_probability binary prime primePlan binaryNodes primeNodes repr shape setup cfg
    binaryRequest metadata request H draw logical core masks primeTape frontend statement fits bodyFits active prior
  rw [OraclePrimaryFreshness.gf128_mask_denominator (binary_card binary)] at bound
  exact bound.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr budget) (by positivity))

include bodyFits in
/-- An aborting runtime need only agree with the explicit real-response
constructor on its successful branch. This is a literal key identity; the
counting proof supplies all freshness and entropy reasoning itself. -/
theorem active_input_queries (active : (Fin 361 → B) → Prop) (actualInput : (Fin 361 → B) → Bytes)
    (onActive : ∀ sample, active sample → actualInput sample =
      input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
        logical core masks primeTape frontend statement fits sample)
    (prior : Finset Bytes) (queries : ℕ) (budget : prior.card ≤ queries) :
    ((Finset.univ.filter fun sample : Mask => active sample ∧ actualInput sample ∈ prior).card : ℚ) /
      (2 : ℚ)^46208 ≤ (queries : ℚ)/(2 : ℚ)^46208 := by
  have events : (Finset.univ.filter fun sample : Mask => active sample ∧ actualInput sample ∈ prior) =
      (Finset.univ.filter fun sample : Mask => active sample ∧
        input binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
          logical core masks primeTape frontend statement fits sample ∈ prior) := by
    ext sample
    by_cases enabled : active sample
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,enabled,true_and,onActive sample enabled]
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,enabled,false_and]
  rw [events]
  exact active_raw_queries binary prime primePlan binaryNodes primeNodes repr shape setup cfg binaryRequest metadata request H draw
    logical core masks primeTape frontend statement fits bodyFits active prior queries budget

end LfzkV2.Current.ZeroKnowledge.OracleJointPrimaryFreshness
