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

theorem encode_injective : Function.Injective codec.encode := by
  intro p q h
  exact Option.some.inj (by rw [← codec.decode_encode p,← codec.decode_encode q,h])

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

theorem fixLeft_program [DecidableEq QL] (outside : Raw → A) {TL left right : ℕ}
    (tape : Fin TL → DL) (dflt : DL)
    (body : TwoOracleTree QL DL Raw A Out left right) (seen : List QL) :
    fixLeft tape dflt (codec.program outside body) seen = codec.tree outside (fixLeft tape dflt body seen) := by
  induction body generalizing seen with
  | done out => rfl
  | queryLeft query next ih =>
      simp only [program,fixLeft]
      exact ih _ _
  | queryRight raw next ih =>
      cases hd : codec.decode raw with
      | none => simp only [program,hd,fixLeft_weakenRight,fixLeft,tree]; rw [ih]
      | some point =>
          simp only [program,hd,fixLeft,tree]
          exact congrArg (Tree.query point.val) (funext fun answer => ih answer seen)

/-- State-enriched fixing retains the complete lazy Merkle slot list in
addition to the output and the ordered canonical right-query trace. -/
theorem fixLeftState_program [DecidableEq QL] (outside : Raw → A) {TL left right : ℕ}
    (tape : Fin TL → DL) (dflt : DL)
    (body : TwoOracleTree QL DL Raw A Out left right) (seen : List QL) :
    fixLeftState tape dflt (codec.program outside body) seen =
      codec.tree outside (fixLeftState tape dflt body seen) := by
  induction body generalizing seen with
  | done out => rfl
  | queryLeft query next ih =>
      simp only [program,fixLeftState]
      exact ih _ _
  | queryRight raw next ih =>
      cases hd : codec.decode raw with
      | none =>
          have hw : ∀ {left right : ℕ} (p : TwoOracleTree QL DL Point A Out left right) seen,
              fixLeftState tape dflt (weakenRight p) seen = (fixLeftState tape dflt p seen).weaken := by
            intro left right p
            induction p with
            | done out => intro seen; rfl
            | queryLeft q next ih => intro seen; simp only [weakenRight,fixLeftState]; exact ih _ _
            | queryRight q next ih =>
                intro seen
                simp only [weakenRight,fixLeftState,Tree.weaken]
                exact congrArg (Tree.query q) (funext fun answer => ih answer seen)
          simp only [program,hd,hw,fixLeftState,tree]
          rw [ih]
      | some point =>
          simp only [program,hd,fixLeftState,tree]
          exact congrArg (Tree.query point.val) (funext fun answer => ih answer seen)

theorem left_state_preserved [DecidableEq QL] (outside : Raw → A) (H : Point → A)
    {TL left right : ℕ} (tape : Fin TL → DL) (dflt : DL)
    (body : TwoOracleTree QL DL Raw A Out left right) (seen : List QL) :
    ((fixLeftState tape dflt (codec.program outside body) seen).run H).1 =
      ((fixLeftState tape dflt body seen).run (codec.oracle outside H)).1 := by
  rw [fixLeftState_program,run_tree]

/-- The queried-support bound used by the typed FS theorem holds with the
same raw budget. Outside-image calls are charged by neither extra typed
queries nor invented protocol rounds. -/
theorem program_seen_card_le [DecidableEq QL] [DecidableEq Raw] [DecidableEq Point]
    (outside : Raw → A) (H : Point → A) {TL left right : ℕ}
    (tape : Fin TL → DL) (dflt : DL)
    (body : TwoOracleTree QL DL Raw A Out left right) (seen : List QL) :
    (TranscriptV2.seen (fixLeft tape dflt (codec.program outside body) seen) H).card ≤
      (TranscriptV2.seen (fixLeft tape dflt body seen) (codec.oracle outside H)).card := by
  rw [fixLeft_program]
  exact codec.seen_card_le outside H _


section ContextCut
variable {Key : Type} [DecidableEq Key]

/-- Stop before the first typed query naming a commitment context, while
retaining every preceding Merkle query in its original order. -/
def typedCut (key : Point → Key) (target : Key) (H : Point → A) : {left right : ℕ} →
    TwoOracleTree QL DL Point A Out left right → Tree QL DL (Option Point) left
  | _, _, .done _ => .done none
  | _, _, .queryLeft query next => .query query fun answer => typedCut key target H (next answer)
  | _, _, .queryRight point next =>
      if key point = target then .done (some point) else typedCut key target H (next (H point))

/-- Unrelated bytes have no parsed protocol context. They are evaluated
locally, rather than moving the cut past a valid query that names the key. -/
def rawCut (codec : Codec Point Raw valid) (key : Point → Key) (target : Key)
    (outside : Raw → A) (H : Point → A) : {left right : ℕ} →
    TwoOracleTree QL DL Raw A Out left right → Tree QL DL (Option Point) left
  | _, _, .done _ => .done none
  | _, _, .queryLeft query next => .query query fun answer => codec.rawCut key target outside H (next answer)
  | _, _, .queryRight raw next => match codec.decode raw with
    | none => codec.rawCut key target outside H (next (outside raw))
    | some point => if key point.val = target then .done (some point.val)
        else codec.rawCut key target outside H (next (H point.val))

private theorem typedCut_weakenRight (key : Point → Key) (target : Key) (H : Point → A)
    {left right : ℕ} (body : TwoOracleTree QL DL Point A Out left right) :
    typedCut key target H (weakenRight body) = typedCut key target H body := by
  induction body with
  | done _ => rfl
  | queryLeft query next ih =>
      simp only [typedCut,weakenRight]
      exact congrArg (Tree.query query) (funext ih)
  | queryRight point next ih =>
      simp only [typedCut,weakenRight]
      split_ifs with h
      · rfl
      · exact ih (H point)

/-- Equality of the whole cut program preserves both its stopping point
and every Merkle answer used by a context-based extractor. -/
theorem cut_program (key : Point → Key) (target : Key) (outside : Raw → A) (H : Point → A)
    {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) :
    typedCut key target H (codec.program outside body) = codec.rawCut key target outside H body := by
  induction body with
  | done _ => rfl
  | queryLeft query next ih =>
      simp only [program,typedCut,rawCut]
      exact congrArg (Tree.query query) (funext ih)
  | queryRight raw next ih =>
      cases hd : codec.decode raw with
      | none => simp only [program,hd,typedCut_weakenRight,rawCut]; exact ih (outside raw)
      | some point =>
          simp only [program,hd,typedCut,rawCut]
          split_ifs with h
          · rfl
          · exact ih (H point.val)

theorem cut_trace (key : Point → Key) (target : Key) (outside : Raw → A) (H : Point → A)
    {left right : ℕ} (body : TwoOracleTree QL DL Raw A Out left right) (HM : QL → DL) :
    (typedCut key target H (codec.program outside body)).run HM =
      (codec.rawCut key target outside H body).run HM := by
  rw [cut_program]

theorem extractor_preserved {Witness : Type} (key : Point → Key) (target : Key)
    (outside : Raw → A) (H : Point → A) {left right : ℕ}
    (body : TwoOracleTree QL DL Raw A Out left right) (HM : QL → DL)
    (extractor : Option Point × List (QL × DL) → Witness) :
    extractor ((typedCut key target H (codec.program outside body)).run HM) =
      extractor ((codec.rawCut key target outside H body).run HM) := by
  rw [cut_trace]

end ContextCut


section FiniteWindow
variable [Fintype A] [Fintype DL] [DecidableEq Raw]

/-- The finite set of all raw queries in a bounded program, across every
answer branch. This does not require the byte-string space to be finite. -/
def allQueries : {left right : ℕ} → TwoOracleTree QL DL Raw A Out left right → Finset Raw
  | _, _, .done _ => ∅
  | _, _, .queryLeft _ next => univ.biUnion fun answer => allQueries (next answer)
  | _, _, .queryRight raw next => insert raw (univ.biUnion fun answer => allQueries (next answer))

theorem queried_mem_allQueries [DecidableEq QL] {TL left right : ℕ}
    (tape : Fin TL → DL) (dflt : DL) (body : TwoOracleTree QL DL Raw A Out left right)
    (seen : List QL) (H : Raw → A) (raw : Raw)
    (h : raw ∈ Bcs.TotalOracle.queried (fixLeft tape dflt body seen) H) : raw ∈ allQueries body := by
  induction body generalizing seen with
  | done out => simp only [fixLeft,Bcs.TotalOracle.queried,Tree.run_done,List.map_nil,List.not_mem_nil] at h
  | queryLeft query next ih =>
      simp only [fixLeft] at h
      exact mem_biUnion.mpr ⟨_,mem_univ _,ih _ _ h⟩
  | queryRight query next ih =>
      simp only [fixLeft,Bcs.TotalOracle.queried_query,List.mem_cons] at h
      rcases h with rfl | h
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_biUnion.mpr ⟨H query,mem_univ _,ih _ _ h⟩)

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

/-- A completed raw execution uses only this finite window, for every
oracle and every lazy Merkle tape. Thus restricting the raw oracle to it
preserves the whole execution trace, not only the accepted output. -/
theorem run_window [DecidableEq QL] {TL left right : ℕ}
    (tape : Fin TL → DL) (dflt : DL) (body : TwoOracleTree QL DL Raw A Out left right)
    (seen : List QL) (H : Raw → A) (fallback : Raw → A) :
    (fixLeft tape dflt body seen).run
      (fun raw => if h : raw ∈ codec.window body then H (show {r // r ∈ codec.window body} from ⟨raw,h⟩).val else fallback raw) =
      (fixLeft tape dflt body seen).run H := by
  apply Tree.run_congr_on_trace
  intro qa hqa
  have hmem : qa.1 ∈ codec.window body := mem_union_left _
    (queried_mem_allQueries tape dflt body seen H qa.1
      (List.mem_map.mpr ⟨qa,hqa,rfl⟩))
  rw [dif_pos hmem]
  exact (Tree.trace_sound _ H qa hqa).symm

end FiniteWindow

end Interleaving

end Codec
end LfzkV2.Current.ByteOracleTransport
