import TranscriptV2.Queries
import Merkle.TwoOracle

/-! Transport a byte-oracle program onto canonical typed query prefixes.
Only valid prefixes have encodings. Malformed or unrelated byte queries are
answered by a separately fixed oracle; they consume no typed query. The
codec does not tag an early prefix with any public value bound only later. -/
noncomputable section
namespace LfzkV2.Current.ByteOracleTransport
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Finset
open scoped Classical

variable {Point Raw A Out : Type} {valid : Point → Prop}

/-- A partial inverse on canonical queries. The second law prevents two
raw strings from being aliases for one canonical query. It makes no claim
about ill-formed typed inputs outside `valid`. -/
structure Codec (Point Raw : Type) (valid : Point → Prop) where
  encode : {point // valid point} → Raw
  decode : Raw → Option {point // valid point}
  decode_encode : ∀ point, decode (encode point) = some point
  encode_decode : ∀ raw point, decode raw = some point → encode point = raw

namespace Codec
variable (codec : Codec Point Raw valid)

/-- Retain auxiliary queries while exposing canonical queries to protocol
lemmas. Unused noncanonical typed coordinates may be padded independently;
the translated program never asks them. -/
def tag (raw : Raw) : Point ⊕ Raw :=
  match codec.decode raw with
  | some point => .inl point.val
  | none => .inr raw

/-- Recover the original address from either branch. Noncanonical typed
coordinates have no raw preimage and therefore contribute no trace entry. -/
def untag : Point ⊕ Raw → Option Raw
  | .inl point => if h : valid point then some (codec.encode ⟨point,h⟩) else none
  | .inr raw => some raw

theorem untag_tag (raw : Raw) : codec.untag (codec.tag raw) = some raw := by
  cases found : codec.decode raw with
  | none => simp only [tag,found,untag]
  | some point =>
      simp only [tag,found,untag,dif_pos point.property]
      exact congrArg some (codec.encode_decode raw point found)

theorem tag_injective : Function.Injective codec.tag := by
  intro first second same
  exact Option.some.inj ((codec.untag_tag first).symm.trans
    ((congrArg codec.untag same).trans (codec.untag_tag second)))

/-- Context labels are unchanged when canonical addresses become typed
coordinates. Auxiliary names retain their original labels. -/
theorem tag_label {Key : Type} (label : Point → Key) (rawLabel : Raw → Option Key)
    (compatible : ∀ raw point, codec.decode raw = some point → rawLabel raw = some (label point.val))
    (raw : Raw) :
    Sum.elim (some ∘ label) rawLabel (codec.tag raw) = rawLabel raw := by
  cases found : codec.decode raw with
  | none => simp only [tag,found,Sum.elim_inr]
  | some point =>
      simpa only [tag,found,Sum.elim_inl,Function.comp_apply] using (compatible raw point found).symm

def oracle (outside : Raw → A) (H : Point → A) (raw : Raw) : A :=
  match codec.decode raw with
  | some point => H point.val
  | none => outside raw

@[simp] theorem oracle_encode (outside : Raw → A) (H : Point → A) (point : {p // valid p}) :
    codec.oracle outside H (codec.encode point) = H point.val := by
  simp only [oracle,codec.decode_encode]

/-- Restrict any raw oracle to its canonical image; unused typed inputs
receive arbitrary auxiliary values. -/
def restrict (rawOracle : Raw → A) (fallback : Point → A) (point : Point) : A :=
  if h : valid point then rawOracle (codec.encode ⟨point,h⟩) else fallback point

@[simp] theorem oracle_restrict (rawOracle : Raw → A) (fallback : Point → A) :
    codec.oracle rawOracle (codec.restrict rawOracle fallback) = rawOracle := by
  funext raw
  unfold oracle
  cases h : codec.decode raw with
  | none => rfl
  | some point =>
      simp only [restrict,dif_pos point.property]
      rw [codec.encode_decode raw point h]

/-- The raw execution trace is filtered, retaining the order and actual
answer at every canonical query. -/
def trace (rawTrace : List (Raw × A)) : List (Point × A) :=
  rawTrace.filterMap fun qa => (codec.decode qa.1).map fun point => (point.val,qa.2)

def tree (codec : Codec Point Raw valid) (outside : Raw → A) : {fuel : ℕ} → Tree Raw A Out fuel → Tree Point A Out fuel
  | _, .done out => .done out
  | _, .query raw next => match codec.decode raw with
    | some point => .query point.val fun answer => codec.tree outside (next answer)
    | none => (codec.tree outside (next (outside raw))).weaken

/-- Fixing the outside oracle is ordinary conditioning. The translated
program has the same output and the exact canonical part of the raw trace. -/
theorem run_tree (outside : Raw → A) (H : Point → A) {fuel : ℕ} (program : Tree Raw A Out fuel) :
    (codec.tree outside program).run H =
      ((program.run (codec.oracle outside H)).1,codec.trace (program.run (codec.oracle outside H)).2) := by
  induction program with
  | done out => rfl
  | query raw next ih =>
      cases hd : codec.decode raw with
      | none =>
          simp only [tree,hd,Tree.run_weaken,oracle,Tree.run_query,trace,List.filterMap_cons,Option.map_none]
          exact ih (outside raw)
      | some point =>
          simp only [tree,hd,Tree.run_query,oracle,trace,List.filterMap_cons,Option.map_some]
          rw [ih (H point.val)]
          rfl

/-- Every queried typed point comes from an actually queried raw string. -/
theorem queried_tree (outside : Raw → A) (H : Point → A) {fuel : ℕ} (program : Tree Raw A Out fuel) :
    Bcs.TotalOracle.queried (codec.tree outside program) H =
      (Bcs.TotalOracle.queried program (codec.oracle outside H)).filterMap
        (fun raw => (codec.decode raw).map Subtype.val) := by
  rw [Bcs.TotalOracle.queried,run_tree]
  simp only [trace,Bcs.TotalOracle.queried,List.map_filterMap,List.filterMap_map,Option.map_map,Function.comp_def]

/-- Distinct canonical inputs cannot outnumber distinct raw inputs, even
when malformed and repeated raw calls are interleaved adaptively. -/
theorem seen_card_le [DecidableEq Point] [DecidableEq Raw] (outside : Raw → A) (H : Point → A)
    {fuel : ℕ} (program : Tree Raw A Out fuel) :
    (TranscriptV2.seen (codec.tree outside program) H).card ≤
      (TranscriptV2.seen program (codec.oracle outside H)).card := by
  let source := TranscriptV2.seen program (codec.oracle outside H)
  have hsubset : TranscriptV2.seen (codec.tree outside program) H ⊆
      source.biUnion (fun raw => ((codec.decode raw).map Subtype.val).toFinset) := by
    intro point hp
    rw [TranscriptV2.seen,queried_tree] at hp
    obtain ⟨raw,hraw,hpoint⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hp)
    exact mem_biUnion.mpr ⟨raw,List.mem_toFinset.mpr hraw,by simpa using hpoint⟩
  apply (card_le_card hsubset).trans
  apply (card_biUnion_le).trans
  calc
    ∑ raw ∈ source, (((codec.decode raw).map Subtype.val).toFinset).card ≤ ∑ _raw ∈ source, 1 := by
      apply sum_le_sum
      intro raw _
      cases codec.decode raw <;> simp
    _ = source.card := by simp


section Interleaving
variable {QL DL : Type}

/-- Left-oracle work is retained in place, including repeated Merkle calls.
Only outside-image right calls become local conditioned computation. -/
def program (codec : Codec Point Raw valid) (outside : Raw → A) : {left right : ℕ} →
    TwoOracleTree QL DL Raw A Out left right → TwoOracleTree QL DL Point A Out left right
  | _, _, .done out => .done out
  | _, _, .queryLeft query next => .queryLeft query fun answer => codec.program outside (next answer)
  | _, _, .queryRight raw next => match codec.decode raw with
    | some point => .queryRight point.val fun answer => codec.program outside (next answer)
    | none => weakenRight (codec.program outside (next (outside raw)))


section FiniteWindow
variable [Fintype A] [Fintype DL] [DecidableEq Raw]

/-- The finite set of all raw queries in a bounded program, across every
answer branch. This does not require the byte-string space to be finite. -/
def allQueries : {left right : ℕ} → TwoOracleTree QL DL Raw A Out left right → Finset Raw
  | _, _, .done _ => ∅
  | _, _, .queryLeft _ next => univ.biUnion fun answer => allQueries (next answer)
  | _, _, .queryRight raw next => insert raw (univ.biUnion fun answer => allQueries (next answer))

variable [Fintype {point // valid point}]

/-- Add all canonical verifier inputs to the program's all-branches query
set. Uniform sampling on this finite window is the relevant finite marginal
of a random oracle on arbitrary byte strings. -/
def window {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) : Finset Raw :=
  allQueries body ∪ (univ.image codec.encode)

theorem encode_mem_window {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right)
    (point : {p // valid p}) : codec.encode point ∈ codec.window body :=
  mem_union_right _ (mem_image_of_mem _ (mem_univ point))

/-- Restrict the partial codec to the explicit finite marginal. No maximum
length or finite universe of all adversarial byte strings is assumed. -/
def windowCodec {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) :
    Codec Point {raw // raw ∈ codec.window body} valid where
  encode point := ⟨codec.encode point,codec.encode_mem_window body point⟩
  decode raw := codec.decode raw.val
  decode_encode := codec.decode_encode
  encode_decode raw point h := Subtype.ext (codec.encode_decode raw.val point h)

end FiniteWindow

end Interleaving

end Codec
end LfzkV2.Current.ByteOracleTransport
