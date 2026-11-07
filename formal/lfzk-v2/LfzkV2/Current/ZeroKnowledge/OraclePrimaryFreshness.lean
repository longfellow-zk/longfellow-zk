import LfzkV2.Current.ZeroKnowledge.OracleResponse
import LfzkV2.Current.ZeroKnowledge.OracleBytes
import LfzkV2.Current.ZeroKnowledge.BackendProfile

/-! The actual canonical opening input pins the binary primary-mask samples.
All other backend coins and the pre-proof oracle are fixed. The commitment
root and the entire frontend prefix may depend arbitrarily on that mask.

The constructor samples fstar at the 361 transmitted H nodes, obtains the
batching coin from the actual earlier canonical preimage, and fills the
existing response arrays using the honest or dummy backend algorithm. Decoding a candidate
opening input recovers that same batching ancestor. Thus its primary array
determines fstar uniquely. No root-entropy or response-formula certificate is
assumed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OraclePrimaryFreshness
open Polynomial LigeroFamily RecursivePolygero.Local
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B]

def nodes (domain : Fin 2792 ↪ B) (i : Fin 361) : B :=
  domain ⟨349+i.val,by have := i.isLt; omega⟩

omit [Field B] [Fintype B] [DecidableEq B] in
theorem nodes_injective (domain : Fin 2792 ↪ B) : Function.Injective (nodes domain) := by
  intro i j equal
  have values := congrArg Fin.val (domain.injective equal)
  apply Fin.ext
  change 349+i.val = 349+j.val at values
  omega

abbrev ProfileStatement (domain : Fin 2792 ↪ B) (cells count : ℕ) :=
  ((ConcreteSetup.backend domain cells).indexed count).backend.layer.Statement

abbrev ProfileCoin (domain : Fin 2792 ↪ B) (cells count : ℕ) :=
  ((ConcreteSetup.backend domain cells).indexed count).backend.layer.Coin

/-- `none` is the dummy commitment used by the simulator. `some` retains
the honest logical cells for the causal opening refresh. -/
def sourceMessages {cells : ℕ} (logical : Option (Backend.Cells B (ConcreteSetup.rows cells) 265)) :
    PolygeroCoreMasking.Messages B 265 0 (ConcreteSetup.rows cells) 0 :=
  match logical with
  | none => 0
  | some values => Backend.messages values

omit [Field B] [DecidableEq B] in
/-- The binary primary mask has 361 independently sampled field cells. -/
theorem gf128_mask_card (card : Fintype.card B = 2^128) :
    Fintype.card (Fin 361 → B) = 2^46208 := by
  rw [Fintype.card_fun,Fintype.card_fin,card,← pow_mul]

omit [Field B] [DecidableEq B] in
theorem gf128_mask_denominator (card : Fintype.card B = 2^128) :
    (Fintype.card B : ℚ)^361 = (2 : ℚ)^46208 := by
  rw [card,Nat.cast_pow,Nat.cast_ofNat,← pow_mul]

variable {g : Geometry} {fields : Fields} {Advice C : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → fields .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount)
variable (initial : Digest)
local notation "Output" => CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "Encoding" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request
variable (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)
variable (binary : fields .binary ≃ B)
variable (rowDimension : g.rowDimension = 349) (maskingDegree : g.maskingDegree = 12)

def primaryLength : g.rowDimension+g.maskingDegree = 361 := by rw [rowDimension,maskingDegree]
def arithmeticLength : 2*g.rowDimension = 698 := by rw [rowDimension]

def decodePrimary (primary : Fin (g.rowDimension+g.maskingDegree) → fields .binary) : Fin 361 → B :=
  fun i => binary (primary (Fin.cast (primaryLength rowDimension maskingDegree).symm i))

variable (domain : Fin 2792 ↪ B) (cells count : ℕ)
local notation "G" => Backend.profileGeometry domain
local notation "Mask" => Fin 361 → B
local notation "Statement" => ProfileStatement domain cells count
local notation "Coin" => ProfileCoin domain cells count

variable (logical : Option (Backend.Cells B (ConcreteSetup.rows cells) 265))
variable (draw : C → Fin (BackendChallenges.size count (ConcreteSetup.rows cells) 12) → B)
variable (core : PolygeroCoreMasking.Tape B 84 (ConcreteSetup.rows cells) 0)
variable (masks : PolygeroMasking.Tape (Backend.profileGeometry domain).code (PolygeroZk.sumFunctional B 265))

/-- Exactly the binary part of the current joint batching decoder. -/
def coinAt (point : Point) : ProfileCoin domain cells count :=
  (BackendChallenges.fieldEquiv (ConcreteSetup.backend domain cells) count (show 0 < 349 by decide))
    (draw (H point).2)

def batchPart (point : Point) : Mask := fun i =>
  (PolygeroPrimaryMasking.batch (G).positive (coinAt repr shape setup publicCount H domain cells count draw point).2
    (PolygeroZk.ordinaryRows (G) (sourceMessages logical) core masks) : B[X]).eval (nodes domain i)

/-- A candidate's strict batching ancestor fixes its non-fstar batch even
when the candidate's commitment root depends on fstar. -/
def base (point : Point) : Mask :=
  match point.atRank g.batchingIndex.val with
  | none => 0
  | some parent => batchPart repr shape setup publicCount H domain cells count logical draw core masks parent

variable (pending : (Fin 361 → B) → CanonicalRequest.Output (g := g) (fields := fields) (Advice := Advice))
variable (statement : (Fin 361 → B) → ProfileStatement domain cells count)
variable (query : (Fin 361 → B) → QuerySet 2443 84)

def batching (sample : Mask) : Point :=
  ((Encoding).chain initial).point (pending sample) H g.batchingIndex.val

def view (sample : Mask) : Backend.View (F := B) 265 (ConcreteSetup.rows cells) 12 (query sample) :=
  let coin := coinAt repr shape setup publicCount H domain cells count draw
    (batching repr shape setup publicCount binaryRequest metadata request initial H pending sample)
  let tape := (core,masks,(Response.evaluationEquiv B (nodes domain) (nodes_injective domain)).symm sample)
  match logical with
  | none => Backend.profileSimulate domain cells count (query sample) (statement sample) coin tape
  | some values => Backend.real (Backend.profileGeometry domain) (query sample) values (statement sample) coin tape

def wireResponse (sample : Mask) : Response g (fields .binary) where
  h i := binary.symm ((Backend.responseSamples domain
    (view repr shape setup publicCount binaryRequest metadata request initial H domain cells count logical draw
      core masks pending statement query sample)).1 (Fin.cast (primaryLength rowDimension maskingDegree) i))
  z i := binary.symm ((Backend.responseSamples domain
    (view repr shape setup publicCount binaryRequest metadata request initial H domain cells count logical draw
      core masks pending statement query sample)).2 (Fin.cast (arithmeticLength rowDimension) i))

def proof (sample : Mask) : Output :=
  OracleResponse.proof (pending sample)
    (wireResponse repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query sample)

def historyOf (sample : Mask) : Point :=
  ((Encoding).chain initial).point
    (proof repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query sample) H g.openingIndex.val

theorem base_history (sample : Mask) :
    base repr shape setup publicCount H domain cells count logical draw core masks
      (historyOf repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
        domain cells count logical draw core masks pending statement query sample) =
      batchPart repr shape setup publicCount H domain cells count logical draw core masks
        (batching repr shape setup publicCount binaryRequest metadata request initial H pending sample) := by
  unfold base historyOf
  rw [(Encoding).point_atRank initial _ H g.openingIndex.val g.batchingIndex.val
    (Nat.le_of_lt g.openingIndex.isLt) (by have := g.openingIndex_val; omega)]
  rw [proof,OracleResponse.batching_point repr shape setup publicCount binaryRequest metadata request]
  rfl

theorem primary_formula (sample : Mask) :
    decodePrimary binary rowDimension maskingDegree
        (wireResponse repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
          domain cells count logical draw core masks pending statement query sample).h =
      sample + batchPart repr shape setup publicCount H domain cells count logical draw core masks
        (batching repr shape setup publicCount binaryRequest metadata request initial H pending sample) := by
  funext i
  simp only [decodePrimary,wireResponse,Fin.cast_cast,Fin.cast_refl,Equiv.apply_symm_apply]
  cases logical with
  | none =>
      unfold view Backend.profileSimulate Backend.responseSamples
      exact (Backend.simulate_primary_sample (Backend.profileGeometry domain) (query sample) 0 (statement sample)
        (coinAt repr shape setup publicCount H domain cells count draw
          (batching repr shape setup publicCount binaryRequest metadata request initial H pending sample))
        core masks (nodes domain) (nodes_injective domain) sample i).trans (add_comm _ _)
  | some values =>
      unfold view Backend.responseSamples
      exact (Backend.real_primary_sample (Backend.profileGeometry domain) (query sample) values (statement sample)
        (coinAt repr shape setup publicCount H domain cells count draw
          (batching repr shape setup publicCount binaryRequest metadata request initial H pending sample))
        core masks (nodes domain) (nodes_injective domain) sample i).trans (add_comm _ _)

variable (fits : g.roles.length < 2^64)
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)

def input (sample : Mask) : Bytes :=
  OracleBytes.openingBytes repr shape setup publicCount fits binaryRequest metadata request initial
    (proof repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query sample) H

def read (raw : Bytes) : Option (Point × Mask) :=
  (OracleBytes.taggedPrimary repr shape setup publicCount fits .binary raw).map fun value =>
    (value.1,decodePrimary binary rowDimension maskingDegree value.2)

include bodyFits in
theorem decoded_formula (sample : Mask) :
    read repr shape setup publicCount binary rowDimension maskingDegree fits
        (input repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
          domain cells count logical draw core masks pending statement query fits sample) =
      some (OpeningFreshness.taggedResponse
        (historyOf repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
          domain cells count logical draw core masks pending statement query)
        (base repr shape setup publicCount H domain cells count logical draw core masks) sample) := by
  unfold read input
  rw [OracleBytes.opening_tagged_binary repr shape setup publicCount fits binaryRequest metadata bodyFits]
  change some (_,decodePrimary binary rowDimension maskingDegree
    (wireResponse repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query sample).h) = _
  rw [primary_formula,← base_history]
  rfl

include bodyFits in
/-- Every arbitrary prior byte query guesses at most one of the 361-cell
uniform primary masks. The root may depend arbitrarily on the whole mask. -/
theorem raw_hit_probability (prior : Finset Bytes) :
    ((Finset.univ.filter fun sample : Mask =>
        input repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
          domain cells count logical draw core masks pending statement query fits sample ∈ prior).card : ℚ) /
        (Fintype.card B)^361 ≤ (prior.card : ℚ)/(Fintype.card B)^361 := by
  have bound := OracleBytes.raw_hit_probability
    (historyOf repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query)
    (base repr shape setup publicCount H domain cells count logical draw core masks)
    (input repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query fits)
    (read repr shape setup publicCount binary rowDimension maskingDegree fits)
    (decoded_formula repr shape setup publicCount binaryRequest metadata request initial H binary rowDimension maskingDegree
      domain cells count logical draw core masks pending statement query fits bodyFits) prior
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using bound

end LfzkV2.Current.ZeroKnowledge.OraclePrimaryFreshness
