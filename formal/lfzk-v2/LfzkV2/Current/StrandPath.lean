import LfzkV2.Current.StrandSearch
import TranscriptV2.Composition

/-! Recover the chronological parent queries of decoded logical inputs.
The history table is justified by the actual labelled trace. No accepted-path
order or parent-query certificate is assumed. -/
noncomputable section
namespace LfzkV2.Current.StrandPath
open Finset Merkle.RandomOracle TranscriptV2
open TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T : Type}
variable (schema : Strand.History.Codec T)
variable (bytes : P → Framing.Bytes)

local notation "Name" => StrandSearch.Name P T
local notation "Answer" => Sample Digest Word
local notation "decodeFull" => schema.decode
local notation "name" => StrandSearch.name schema bytes
local notation "advance" => StrandSearch.advance bytes

theorem advance_subset (past : List Strand.Entry) (point : SamplePoint P PrfKey) (answer : Answer) :
    past ⊆ advance past point answer := by
  cases point with
  | inr _ => exact List.Subset.refl _
  | inl point => exact record_subset past (bytes point) answer.1

theorem fold_subset (past : List Strand.Entry) (trace : List (Name × Answer)) :
    past ⊆ trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) past := by
  induction trace generalizing past with
  | nil => exact List.Subset.refl _
  | cons qa rest ih => exact (advance_subset bytes past _ _).trans (ih _)

theorem closed_fold (past : List Strand.Entry) (trace : List (Name × Answer))
    (closed : Closed past) :
    Closed (trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) past) := by
  induction trace generalizing past with
  | nil => exact closed
  | cons qa rest ih =>
      apply ih
      rcases qa with ⟨point,answer⟩
      cases point with
      | inr _ => exact closed
      | inl point => exact record_closed past closed (bytes point.1) answer.1

/-- An ordinary query inserts its decoded history, and later queries never
remove it. This is the converse of the registry's query-support invariant. -/
theorem ordinary_recorded (past : List Strand.Entry) (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase past trace)
    (raw : P) (value : T) (answer : Answer)
    (member : ((.inl (raw,some value),answer) : Name × Answer) ∈ trace) :
    (⟨schema.encode value,answer.1⟩ : Strand.Entry) ∈
      trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) past := by
  induction trace generalizing past with
  | nil => cases member
  | cons qa rest ih =>
      rcases List.mem_cons.mp member with same | later
      · cases same
        have parsed : StrandSearch.decode schema bytes past raw = some value :=
          (Prod.mk.inj (Sum.inl.inj named.1)).2
        obtain ⟨history,unfolded,decoded⟩ := Option.bind_eq_some_iff.mp parsed
        have canonical := schema.canonical history value decoded
        apply fold_subset bytes _ rest
        simp only [StrandSearch.erase,StrandSearch.advance,record,unfolded,
          ← canonical,List.mem_append,List.mem_singleton,or_true]
      · exact ih _ named.2 later

/-- Every registry entry comes from a recorded node query. Its logical
payload was decoded then, using that same stored history. -/
def Supported (past : List Strand.Entry) (trace : List (Name × Answer)) : Prop :=
  ∀ entry ∈ past, ∃ point answer,
    ((.inl (point,decodeFull entry.history),answer) : Name × Answer) ∈ trace ∧
      entry.digest = answer.1 ∧ entry.history.input.encode = bytes point

theorem Supported.mono {past : List Strand.Entry} {first second : List (Name × Answer)}
    (support : Supported schema bytes past first)
    (subset : ∀ qa ∈ first, qa ∈ second) : Supported schema bytes past second := by
  intro entry member
  obtain ⟨point,answer,recorded,digest,encoded⟩ := support entry member
  exact ⟨point,answer,subset _ recorded,digest,encoded⟩

theorem Supported.advance {past : List Strand.Entry} {trace : List (Name × Answer)}
    (support : Supported schema bytes past trace)
    (point : SamplePoint P PrfKey) (answer : Answer) :
    Supported schema bytes (advance past point answer)
      (trace ++ [(name past point,answer)]) := by
  have old : Supported schema bytes past
      (trace ++ [(name past point,answer)]) :=
    Supported.mono schema bytes support (fun _ member => List.mem_append_left _ member)
  cases point with
  | inr digest => exact old
  | inl point =>
      cases parsed : unfoldNode past (bytes point) with
      | none => simpa only [StrandSearch.advance,record,parsed] using old
      | some history =>
          intro entry member
          simp only [StrandSearch.advance,record,parsed,List.mem_append,List.mem_singleton] at member
          rcases member with member | rfl
          · exact old entry member
          · refine ⟨point,answer,?_,rfl,(unfoldNode_erases past (bytes point) history parsed).symm⟩
            have named : name past (.inl point) = .inl (point,decodeFull history) := by
              simp [StrandSearch.name,StrandSearch.decode,parsed]
            simp only [named,List.mem_append,List.mem_singleton,or_true]

theorem supported_fold (past : List Strand.Entry) (before trace : List (Name × Answer))
    (support : Supported schema bytes past before)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase past trace) :
    Supported schema bytes
      (trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) past)
      (before ++ trace) := by
  induction trace generalizing past before with
  | nil => simpa only [List.foldl_nil,List.append_nil] using support
  | cons qa rest ih =>
      obtain ⟨head,tail⟩ := named
      have next := Supported.advance schema bytes support (StrandSearch.erase qa.1) qa.2
      rw [head] at next
      simpa only [List.foldl_cons,List.append_assoc,List.singleton_append] using
        ih _ (before ++ [qa]) next tail

theorem trace_supported (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace) :
    Supported schema bytes
      (trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) []) trace := by
  simpa only [List.nil_append] using supported_fold schema bytes [] [] trace
    (fun _ member => nomatch member) named

/-- Consistency follows by recording actual node answers. It requires no
collision-free hash assumption; collisions are considered only when comparing
two recovered histories with the same erased node. -/
theorem consistent_fold (H : Strand.Oracle) (past : List Strand.Entry)
    (trace : List (Name × Answer))
    (initial : ∀ entry ∈ past, entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (answers : ∀ point logical answer, ((.inl (point,logical),answer) : Name × Answer) ∈ trace →
      answer.1 = H (bytes point)) :
    ∀ entry ∈ trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) past,
      entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode := by
  induction trace generalizing past with
  | nil => exact initial
  | cons qa rest ih =>
      have later : ∀ point logical answer, ((.inl (point,logical),answer) : Name × Answer) ∈ rest →
          answer.1 = H (bytes point) :=
        fun point logical answer member => answers point logical answer (List.mem_cons_of_mem _ member)
      rcases qa with ⟨point,answer⟩
      cases point with
      | inr digest => exact ih past initial later
      | inl point =>
          rcases point with ⟨point,logical⟩
          have actual := answers point logical answer List.mem_cons_self
          apply ih _ _ later
          simpa only [StrandSearch.erase,StrandSearch.advance,actual] using
            record_sound past H initial (bytes point)

/-- A recognised logical node has a history consistent with the same SHA
answers that populated the registry. -/
theorem decoded_consistent (H : Strand.Oracle) (past : List Strand.Entry)
    (sound : ∀ entry ∈ past, entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (raw : P) (value : T) (found : StrandSearch.decode schema bytes past raw = some value) :
    (schema.encode value).Consistent H := by
  obtain ⟨history,unfolded,parsed⟩ := Option.bind_eq_some_iff.mp found
  rw [schema.canonical history value parsed]
  exact unfoldNode_consistent past H sound (bytes raw) history unfolded

/-- Comparing a recovered name with the verifier's actual node needs only
collisions among their queried ancestors. No global injectivity of SHA is
assumed, and the codec need not serialize arbitrary verifier caches. -/
theorem decoded_matches (H : Strand.Oracle) (past : List Strand.Entry)
    (sound : ∀ entry ∈ past, entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (raw : P) (value expected : T) (found : StrandSearch.decode schema bytes past raw = some value)
    (actual : (schema.encode expected).Consistent H)
    (encoded : bytes raw = (schema.encode expected).input.encode)
    (collisionFree : ∀ a ∈ (schema.encode value).ancestors,
      ∀ b ∈ (schema.encode expected).ancestors, H a = H b → a = b) : value = expected := by
  apply schema.encode_injective
  exact Strand.History.erasure_injective H (schema.encode value) (schema.encode expected)
    (decoded_consistent schema bytes H past sound raw value found) actual collisionFree
    ((StrandSearch.decode_erases schema bytes past raw value found).trans encoded)

/-- If a child query has a logical name, its immediate logical parent
already has a matching named query in the preceding trace. This is a
consequence of the decoder and registry, not a query-order assumption. -/
theorem parent_queried_before (before after : List (Name × Answer))
    (raw : P) (child parent : T) (answer : Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase []
      (before ++ ((.inl (raw,some child),answer) : Name × Answer)::after))
    (previous : ∃ digest message, schema.encode child = .child (schema.encode parent) digest message) :
    ∃ point result, ((.inl (point,some parent),result) : Name × Answer) ∈ before := by
  let past := before.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) []
  have supported := trace_supported schema bytes before named.append.1
  have selected := named.name_after
  have parsed : StrandSearch.decode schema bytes past raw = some child := by
    exact (Prod.mk.inj (Sum.inl.inj selected)).2
  obtain ⟨history,unfolded,decoded⟩ := Option.bind_eq_some_iff.mp parsed
  have canonical := schema.canonical history child decoded
  obtain ⟨digest,message,childShape⟩ := previous
  rw [← canonical,childShape] at unfolded
  obtain ⟨entry,member,historyEq,_⟩ := unfoldNode_parent past (bytes raw)
    (schema.encode parent) digest message unfolded
  obtain ⟨point,result,queried,_,_⟩ := supported entry member
  rw [historyEq,schema.inverse] at queried
  exact ⟨point,result,queried⟩

/-- Every ordinary name in the trace represents exactly its queried bytes.
In particular a parsed value cannot acquire a second ordinary coordinate by
changing the raw input while retaining the logical name. -/
theorem ordinary_erases (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace)
    (raw : P) (value : T) (answer : Answer)
    (member : ((.inl (raw,some value),answer) : Name × Answer) ∈ trace) :
    (schema.encode value).input.encode = bytes raw := by
  obtain ⟨first,rest,equal⟩ := List.append_of_mem member
  rw [equal] at named
  have selected := named.name_after
  have parsed : StrandSearch.decode schema bytes
      (first.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) []) raw = some value :=
    (Prod.mk.inj (Sum.inl.inj selected)).2
  exact StrandSearch.decode_erases schema bytes _ raw value parsed

variable [DecidableEq P]

/-- A decoded child forces its canonical parent into the actual preceding
search queries. This uses the online parser, rather than an assumed protocol
order or a separate certificate about the adversary's chosen query order. -/
theorem parent_before {Out : Type} {fuel : ℕ} (tree : Tree Name Answer Out fuel)
    (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2)
    (injective : Function.Injective bytes) (locate : T → P)
    (located : ∀ value, bytes (locate value) = (schema.encode value).input.encode)
    (raw : P) (child parent : T)
    (member : (.inl (raw,some child) : Name) ∈ seen tree H)
    (previous : ∃ digest message, schema.encode child = .child (schema.encode parent) digest message) :
    (.inl (locate parent,some parent) : Name) ∈ before tree H (.inl (raw,some child)) := by
  obtain ⟨first,rest,answer,trace,past⟩ := trace_split_before tree H _ member
  rw [trace] at named
  obtain ⟨point,result,queried⟩ := parent_queried_before schema bytes first rest raw child parent answer
    named previous
  have encoded := ordinary_erases schema bytes first named.append.1 point parent result queried
  have same : point = locate parent := injective (encoded.symm.trans (located parent).symm)
  rw [← past,← same]
  exact List.mem_map_of_mem (f := Prod.fst) queried

/-- Once the final logical node is recognized, all earlier protocol nodes
and adjacent-pair ordering follow from decoding. Collisions, speculative
targets, replay, and the final seal are needed only to establish that final
recognition; they are not assumed again for every algebraic round. -/
theorem path_queries {Out : Type} {fuel rounds : ℕ} (tree : Tree Name Answer Out fuel)
    (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2)
    (injective : Function.Injective bytes) (locate : T → P)
    (located : ∀ value, bytes (locate value) = (schema.encode value).input.encode)
    (path : ℕ → T)
    (previous : ∀ i < rounds, ∃ digest message,
      schema.encode (path (i+1)) = .child (schema.encode (path i)) digest message)
    (terminal : (.inl (locate (path rounds),some (path rounds)) : Name) ∈ seen tree H) :
    Composition.PathQueries (rounds := rounds) tree H
      (fun i => .inl (locate (path i),some (path i))) := by
  let point := fun i => (.inl (locate (path i),some (path i)) : Name)
  have step i (within : i < rounds) (child : point (i+1) ∈ seen tree H) :
      point i ∈ before tree H (point (i+1)) :=
    parent_before schema bytes tree H named injective locate located _ _ _ child (previous i within)
  have all := DigestCharging.backward_path (fun i : Fin (rounds+1) => point i.val)
    (fun p => p ∈ seen tree H)
    (fun i child => List.mem_toFinset.mpr (before_subset tree H _ (step i.val i.isLt child))) terminal
  have queried : ∀ i ≤ rounds, point i ∈ seen tree H := fun i within => all ⟨i,by omega⟩
  refine ⟨queried,?_⟩
  intro i within
  exact first_left_of_before tree H _ _ (step i within (queried (i+1) (by omega)))

end LfzkV2.Current.StrandPath
