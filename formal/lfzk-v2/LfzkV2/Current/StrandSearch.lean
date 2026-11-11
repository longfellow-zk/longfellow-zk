import TranscriptV2.StrandUnfolding
import TranscriptV2.StrandInventory
import TranscriptV2.StrandCharging
import Bcs.FiniteProbability

/-! Translate a raw node/PRF search to full logical protocol inputs.

Node histories are decoded only from already obtained node answers. A query
which cannot yet be decoded keeps its auxiliary name, even if a later query
reveals the missing parent. The coupling reserves each challenge stream at
its first node or PRF query and preserves every repeated answer.
-/
noncomputable section
namespace LfzkV2.Current.StrandSearch
open Finset Merkle.RandomOracle TranscriptV2
open TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T Out : Type} [DecidableEq P]
variable (schema : Strand.History.Codec T)
variable (bytes : P → Framing.Bytes)

def key (point : P) (digest : Digest) : PrfKey := Strand.nodeKey (bytes point) digest

local notation "Answer" => Sample Digest Word
local notation "Raw" => Point P PrfKey Word

/-- Keep the raw name in both cases. Erasing a chosen logical name always
recovers the queried bytes, without an injectivity assumption about SHA. -/
abbrev Name (P T : Type) := Sum (P × Option T) PrfKey

def decode (past : List Strand.Entry) (point : P) : Option T := do
  let history ← unfoldNode past (bytes point)
  schema.decode history

omit [DecidableEq P] in
/-- A recovered logical input has exactly the queried node encoding. This
checks the protocol payload as well as the digest-linked history. -/
theorem decode_erases (past : List Strand.Entry) (raw : P) (logical : T)
    (found : decode schema bytes past raw = some logical) :
    (schema.encode logical).input.encode = bytes raw := by
  obtain ⟨history,unfolded,decoded⟩ := Option.bind_eq_some_iff.mp found
  have canonical := schema.canonical history logical decoded
  rw [canonical]
  exact (unfoldNode_erases past (bytes raw) history unfolded).symm

def name (past : List Strand.Entry) : SamplePoint P PrfKey → Name P T
  | .inl point => .inl (point,decode schema bytes past point)
  | .inr digest => .inr digest

def advance (past : List Strand.Entry) (point : SamplePoint P PrfKey) (answer : Answer) : List Strand.Entry :=
  match point with
  | .inl point => record past (bytes point) answer.1
  | .inr _ => past

def erase {T : Type} : Name P T → SamplePoint P PrfKey
  | .inl (point,_) => .inl point
  | .inr digest => .inr digest

omit [DecidableEq P] in
theorem name_erases (past : List Strand.Entry) (point : SamplePoint P PrfKey) :
    erase (name schema bytes past point) = point := by
  cases point <;> rfl

/-- Both internal states survive the proof-submission cut: the sampled
streams and the histories already recovered from node queries. -/
def searchState {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) :
    Tree (Name P T) Answer ((Out × Cache P PrfKey Digest Word) × List Strand.Entry) fuel :=
  FreshOracle.relabel (name schema bytes) (advance bytes) (eagerState (key bytes) program state) past

def search {fuel : ℕ} (program : Tree Raw Digest Out fuel) : Tree (Name P T) Answer Out fuel :=
  (searchState schema bytes program Cache.empty []).map (fun result => result.1.1)

theorem searchState_fresh {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) :
    FreshOracle.FreshFrom (fun point => state.known (erase point))
      (searchState schema bytes program state past) :=
  FreshOracle.relabel_fresh (name schema bytes) (advance bytes) erase (name_erases schema bytes)
    (eagerState (key bytes) program state) state.known past (eagerState_fresh (key bytes) program state)

theorem search_fresh {fuel : ℕ} (program : Tree Raw Digest Out fuel) :
    FreshOracle.FreshFrom (fun _ => False) (search schema bytes program) :=
  ((searchState_fresh schema bytes program Cache.empty []).map (fun result => result.1.1)).mono
    (fun _ h => h.elim)

/-- All stored logical names agree with the canonical decoder at their
actual query time. Later answers cannot retroactively change a name. -/
theorem search_trace {fuel : ℕ} (program : Tree Raw Digest Out fuel) (H : Name P T → Answer) :
    FreshOracle.NamedTrace (name schema bytes) (advance bytes) erase []
      ((search schema bytes program).run H).2 := by
  simpa only [search,searchState,Tree.run_map] using
    FreshOracle.relabel_trace (name schema bytes) (advance bytes) erase (name_erases schema bytes)
      (eagerState (key bytes) program Cache.empty) [] H

/-- Erasing logical labels recovers one execution of the row-sampling
coupling, including its full cache and all sampled coordinates. -/
theorem searchState_samples {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    ∃ sample : SamplePoint P PrfKey → Answer, (eagerState (key bytes) program state).run sample =
      (((searchState schema bytes program state past).run H).1.1,
        ((searchState schema bytes program state past).run H).2.map (fun qa => (erase qa.1,qa.2))) :=
  FreshOracle.relabel_run_exists (name schema bytes) (advance bytes)
    erase (name_erases schema bytes) (eagerState (key bytes) program state) past H
    state.known (eagerState_fresh (key bytes) program state)

/-- The original adversarial search also leaves every obtained node's
stream reserved. Verifier replay may rely on this invariant at its cut. -/
theorem searchState_reserved {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (reserved : state.Reserved (key bytes)) :
    ((searchState schema bytes program state past).run H).1.1.2.Reserved (key bytes) := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  simpa only [run] using eagerState_reserved (key bytes) program state sample reserved

/-- Naming histories preserves the complete fresh-sample trace length.
Any bound established for the raw coupling therefore survives parsing. -/
theorem searchState_length {fuel bound : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (bounded : ∀ sample, ((eagerState (key bytes) program state).run sample).2.length ≤ bound) :
    ((searchState schema bytes program state past).run H).2.length ≤ bound := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  simpa only [run,List.length_map] using bounded sample

/-- Replay extends the original cache; it cannot change an answer retained
at the extraction cut. This includes blocks not consumed by the honest reader. -/
theorem searchState_extends {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    state.Extends ((searchState schema bytes program state past).run H).1.1.2 := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  simpa only [run] using eagerState_extends (key bytes) program state sample

/-- Every raw oracle agreeing with the retained cache reproduces this
execution, including any raw trace explicitly retained in its output. -/
theorem searchState_source {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (G : Raw → Digest)
    (agreement : ((searchState schema bytes program state past).run H).1.1.2.Matches G) :
    (program.run G).1 = ((searchState schema bytes program state past).run H).1.1.1 ∧
      ∀ point logical answer, ((.inl (point,logical),answer) : Name P T × Answer) ∈
        ((searchState schema bytes program state past).run H).2 → G (.inl point) = answer.1 := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  have actual := eagerState_source (key bytes) program state sample G (by simpa only [run] using agreement)
  refine ⟨by simpa only [run] using actual.1,?_⟩
  intro point logical answer member
  apply (actual.2 point answer ?_).1
  rw [run]
  exact List.mem_map_of_mem (f := fun qa : Name P T × Answer => (erase qa.1,qa.2)) member

/-- Every named node comes from an actual raw SHA call in this execution.
Thus collision scope may use the raw queried set; sampled dummy coordinates
at early PRF queries are not silently treated as SHA node outputs. -/
theorem searchState_node_queried {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (G : Raw → Digest)
    (agreement : ((searchState schema bytes program state past).run H).1.1.2.Matches G)
    (point : P) (logical : Option T) (answer : Answer)
    (member : ((.inl (point,logical),answer) : Name P T × Answer) ∈
      ((searchState schema bytes program state past).run H).2) :
    (.inl point : Raw) ∈ Bcs.TotalOracle.queried program G := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  have actual := eagerState_source (key bytes) program state sample G (by simpa only [run] using agreement)
  apply (actual.2 point answer ?_).2
  rw [run]
  exact List.mem_map_of_mem (f := fun qa : Name P T × Answer => (erase qa.1,qa.2)) member

/-- Every cached answer has a source in the earlier cache or in this
execution's queries. In particular a row at the submission cut cannot have
been supplied by the verifier's later replay. -/
theorem searchState_cache_source {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    state.Source (key bytes) (((searchState schema bytes program state past).run H).2.map (fun qa => (erase qa.1,qa.2)))
      ((searchState schema bytes program state past).run H).1.1.2 := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  simpa only [run] using eagerState_source_queries (key bytes) program state sample

theorem searchState_node_cached {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (raw : P) (logical : Option T) (answer : Answer)
    (member : ((.inl (raw,logical),answer) : Name P T × Answer) ∈
      ((searchState schema bytes program state past).run H).2) :
    ((searchState schema bytes program state past).run H).1.1.2.nodes raw = some answer.1 := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  have cached := eagerState_node_cached (key bytes) program state sample raw answer (by
    rw [run]
    exact List.mem_map_of_mem (f := fun qa : Name P T × Answer => (erase qa.1,qa.2)) member)
  simpa only [run] using cached

theorem searchState_fresh_streams {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    FreshStreams (key bytes) (((searchState schema bytes program state past).run H).2.map fun qa => (erase qa.1,qa.2)) := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  simpa only [run] using eagerState_fresh_streams (key bytes) program state sample

/-- Naming cannot give two different answers to the same raw coordinate.
This includes duplicate logical cache aliases outside the canonical image. -/
theorem searchState_answers_eq {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer)
    (first second : Name P T) (a b : Answer)
    (ha : (first,a) ∈ ((searchState schema bytes program state past).run H).2)
    (hb : (second,b) ∈ ((searchState schema bytes program state past).run H).2)
    (same : erase first = erase second) : a = b := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes program state past H
  have answer point value (member : (point,value) ∈ ((searchState schema bytes program state past).run H).2) :
      sample (erase point) = value := by
    symm
    apply Tree.trace_sound (eagerState (key bytes) program state) sample (erase point,value)
    rw [run]
    exact List.mem_map_of_mem (f := fun qa : Name P T × Answer => (erase qa.1,qa.2)) member
  exact (answer first a ha).symm.trans ((congrArg sample same).trans (answer second b hb))

/-- Every raw query recorded at the extraction cut has its actual answer
in the same cut cache, including repeated and previously buffered PRF reads. -/
theorem searchState_raw_covered {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    let cut := ((searchState schema bytes (recordTrace program) state past).run H).1
    ∀ point answer, (point,answer) ∈ cut.1.1.2 → cut.1.2.lookup point = some answer := by
  obtain ⟨sample,run⟩ := searchState_samples schema bytes (recordTrace program) state past H
  simpa only [run] using eagerState_recordTrace_covers (key bytes) program state sample

theorem searchState_node_origin {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (H : Name P T → Answer) (raw : P) (digest : Digest)
    (cached : ((searchState schema bytes program Cache.empty []).run H).1.1.2.nodes raw = some digest) :
    ∃ logical answer, ((.inl (raw,logical),answer) : Name P T × Answer) ∈
      ((searchState schema bytes program Cache.empty []).run H).2 ∧ answer.1 = digest := by
  have source := searchState_cache_source schema bytes program Cache.empty [] H
  rcases source.nodes raw digest cached with impossible | ⟨answer,queried,same⟩
  · cases impossible
  · obtain ⟨⟨point,result⟩,member,equal⟩ := List.mem_map.mp queried
    obtain ⟨input,answerEq⟩ := Prod.mk.inj equal
    cases point with
    | inr _ => cases input
    | inl point =>
        rcases point with ⟨point,logical⟩
        cases Sum.inl.inj input
        cases answerEq
        exact ⟨logical,result,member,same⟩

theorem searchState_stream_origin {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (H : Name P T → Answer) (digest : PrfKey) (row : StrandCoupling.Stream Digest Word)
    (cached : ((searchState schema bytes program Cache.empty []).run H).1.1.2.streams digest = some row) :
    ∃ point answer, (point,answer) ∈ ((searchState schema bytes program Cache.empty []).run H).2 ∧
      streamKey (key bytes) (erase point) answer = digest ∧ answer.2 = row := by
  have source := searchState_cache_source schema bytes program Cache.empty [] H
  rcases source.streams digest row cached with impossible | ⟨point,answer,queried,key,same⟩
  · cases impossible
  · obtain ⟨⟨point',result⟩,member,equal⟩ := List.mem_map.mp queried
    obtain ⟨input,answerEq⟩ := Prod.mk.inj equal
    cases answerEq
    exact ⟨point',result,member,input ▸ key,same⟩

/-- Actual raw node calls are visible to the naming proof even if the raw
program repeated a previously cached call. No logical-name premise is used. -/
theorem searchState_raw_node_visible {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (H : Name P T → Answer) (raw : P) (digest : Digest)
    (queried : ((.inl raw,digest) : Raw × Digest) ∈
      ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1.1.1.2) :
    ∃ logical answer, ((.inl (raw,logical),answer) : Name P T × Answer) ∈
      ((searchState schema bytes (recordTrace program) Cache.empty []).run H).2 ∧ answer.1 = digest :=
  searchState_node_origin schema bytes (recordTrace program) H raw digest
    (searchState_raw_covered schema bytes program Cache.empty [] H (.inl raw) digest queried)

/-- A raw PRF call at the submission cut identifies the cached stream that
answered it. This includes a prequery made before its parent node was known. -/
theorem searchState_raw_prf_cached {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (H : Name P T → Answer) (digest : PrfKey) (counter : Word) (answer : Digest)
    (queried : ((.inr (digest,counter),answer) : Raw × Digest) ∈
      ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1.1.1.2) :
    ∃ row, ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1.1.2.streams digest = some row ∧
      row counter = answer :=
  Option.map_eq_some_iff.mp
    (searchState_raw_covered schema bytes program Cache.empty [] H (.inr (digest,counter)) answer queried)

/-- Reading a seal's PRF block before submission establishes the exact
stream-origin premise used by path recovery. Buffering and repeated raw
reads do not require an extra named query. -/
theorem searchState_raw_prf_origin {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (H : Name P T → Answer) (digest : PrfKey) (counter : Word) (answer : Digest)
    (queried : ((.inr (digest,counter),answer) : Raw × Digest) ∈
      ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1.1.1.2) :
    ∃ point result, (point,result) ∈ ((searchState schema bytes (recordTrace program) Cache.empty []).run H).2 ∧
      streamKey (key bytes) (erase point) result = digest := by
  obtain ⟨row,cached,_⟩ := searchState_raw_prf_cached schema bytes program H digest counter answer queried
  obtain ⟨point,result,member,key,_⟩ := searchState_stream_origin schema bytes (recordTrace program) H digest row cached
  exact ⟨point,result,member,key⟩

/-- Every transformed execution is an execution of one raw SHA table.
This also identifies the node answers used by the history registry; matching
only the final output would not justify reasoning about the accepted path. -/
theorem search_source {fuel : ℕ} (program : Tree Raw Digest Out fuel) (H : Name P T → Answer) :
    ∃ G : Raw → Digest,
      (program.run G).1 = ((search schema bytes program).run H).1 ∧
      ∀ point logical answer, ((.inl (point,logical),answer) : Name P T × Answer) ∈
        ((search schema bytes program).run H).2 → G (.inl point) = answer.1 := by
  let G := ((searchState schema bytes program Cache.empty []).run H).1.1.2.raw 0
  have actual := searchState_source schema bytes program Cache.empty [] H G (Cache.matches_raw _ 0)
  refine ⟨G,?_,?_⟩
  · simpa only [search,Tree.run_map] using actual.1
  · intro point logical answer member
    exact actual.2 point logical answer (by simpa only [search,Tree.run_map] using member)

/-- This is a fresh renaming of the actual raw search, including arbitrary
early PRF queries. No assumption about accepted-path query order is supplied. -/
theorem search_uniform [Fintype P] [Fintype T]
    (value : Out → ℚ) {fuel : ℕ} (program : Tree Raw Digest Out fuel) :
    (∑ H : Name P T → Answer,
      value (((search schema bytes program).run H).1)) /
        (Fintype.card Answer : ℚ)^Fintype.card (Name P T) =
      (∑ H : Raw → Digest, value ((program.run H).1)) /
        (Fintype.card Digest : ℚ)^Fintype.card Raw := by
  unfold search searchState
  simp only [Tree.run_map]
  rw [FreshOracle.relabel_uniform (fun result : Out × Cache P PrfKey Digest Word => value result.1)
    (name schema bytes) (advance bytes) erase (name_erases schema bytes)
    (eagerState (key bytes) program Cache.empty) []
    ((eagerState_fresh (key bytes) program Cache.empty).mono (fun _ h => h.elim))]
  apply Eq.trans ?_ (eager_raw_uniform (P := P) (D := Digest) (I := Word) (Out := Out) (key bytes) value program)
  congr 1
  apply sum_congr rfl
  intro H _
  exact congrArg value (congrArg Prod.fst (eagerState_erases (key bytes) program Cache.empty H))

/-- The observation-law part of the composition interface. Apply this to a
program retaining its extraction cut and replay result, not merely its final
proof bytes, when constructing the complete soundness realization. -/
theorem search_law [Fintype P] [Fintype T]
    (event : Out → Prop) {fuel : ℕ} (program : Tree Raw Digest Out fuel) :
    Bcs.FiniteProbability.density (fun H => event (program.run H).1) =
      Bcs.FiniteProbability.density (fun H => event ((search schema bytes program).run H).1) := by
  have law := search_uniform schema bytes (fun out => if event out then 1 else 0) program
  simpa only [Bcs.FiniteProbability.density,sum_boole,Fintype.card_fun,Nat.cast_pow] using law.symm

/-- Proof submission preserves both caches. The verifier starts from the
actual search state, rather than a fresh independently sampled transcript. -/
theorem searchState_bind {Result : Type} {fuel extra : ℕ}
    (program : Tree Raw Digest Out fuel) (replay : Out → Tree Raw Digest Result extra)
    (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) (H : Name P T → Answer) :
    (searchState schema bytes (program.bind replay) state past).run H =
      ((searchState schema bytes program state past).bind fun cut =>
        searchState schema bytes (replay cut.1.1) cut.1.2 cut.2).run H := by
  unfold searchState
  rw [eagerState_comp,FreshOracle.relabel_bind]

theorem searchState_map {Result : Type} {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (f : Out → Result) (state : Cache P PrfKey Digest Word) (past : List Strand.Entry) :
    searchState schema bytes (program.map f) state past =
      (searchState schema bytes program state past).map (Prod.map (Prod.map f id) id) := by
  unfold searchState
  rw [eagerState_map,FreshOracle.relabel_map]

/-- Preserve the raw search trace at the cut, and then run the verifier
from the same cache and history registry. The verifier's queries occur only
in the observation, not in the adversary tree whose algebraic budget is Q. -/
def replayObservation {Result : Type} {fuel extra : ℕ} (program : Tree Raw Digest Out fuel)
    (replay : Out → Tree Raw Digest Result extra) (H : Name P T → Answer) :
    (Out × List (Raw × Digest)) × (Result × List (Raw × Digest)) :=
  let cut := ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1
  let finish := ((searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2).run H).1
  (cut.1.1,finish.1.1)

/-- The retained cut and verifier traces belong to one raw SHA execution.
Any completion of the final cache works. In particular unused raw coordinates
cannot change either the extraction cut or the verifier's decision. -/
theorem replay_source {Result : Type} {fuel extra : ℕ} (program : Tree Raw Digest Out fuel)
    (replay : Out → Tree Raw Digest Result extra) (H : Name P T → Answer) :
    let cut := ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1
    let finish := ((searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2).run H).1
    ∀ G : Raw → Digest, finish.1.2.Matches G →
      program.run G = cut.1.1 ∧ (replay (program.run G).1).run G = finish.1.1 := by
  let cut := ((searchState schema bytes (recordTrace program) Cache.empty []).run H).1
  let finish := ((searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2).run H).1
  change ∀ G : Raw → Digest, finish.1.2.Matches G →
    program.run G = cut.1.1 ∧ (replay (program.run G).1).run G = finish.1.1
  intro G agreement
  have cutMatches := Cache.Matches.of_extension
    (searchState_extends schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2 H) agreement
  have first := (searchState_source schema bytes (recordTrace program) Cache.empty [] H G cutMatches).1
  have last := (searchState_source schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2 H G agreement).1
  simp only [run_recordTrace] at first last
  refine ⟨first,?_⟩
  rw [first]
  exact last

/-- Joint equality of the extraction-cut and verifier observations. Raw
answers are preserved even when query grouping hides a repeated PRF read
from the logical trace. This is stronger than equality of submitted proofs. -/
theorem replay_law [Fintype P] [Fintype T] {Result : Type} {fuel extra : ℕ}
    (program : Tree Raw Digest Out fuel) (replay : Out → Tree Raw Digest Result extra)
    (event : (Out × List (Raw × Digest)) × (Result × List (Raw × Digest)) → Prop) :
    Bcs.FiniteProbability.density (fun G => event (program.run G,(replay (program.run G).1).run G)) =
      Bcs.FiniteProbability.density (fun H => event (replayObservation schema bytes program replay H)) := by
  let joined := (recordTrace program).bind fun cut =>
    (recordTrace (replay cut.1)).map fun finish => (cut,finish)
  have raw G : (joined.run G).1 = (program.run G,(replay (program.run G).1).run G) := by
    simp only [joined,Tree.run_bind,Tree.run_map,run_recordTrace]
  have coupled H : ((search schema bytes joined).run H).1 =
      replayObservation schema bytes program replay H := by
    simp only [search,Tree.run_map]
    rw [searchState_bind]
    simp only [Tree.run_bind,searchState_map,Tree.run_map,Prod.map,replayObservation]
  have law := search_law schema bytes event joined
  simpa only [raw,coupled] using law

omit [DecidableEq P] in
def auxiliary {T : Type} : Name P T → Prop
  | .inl (_,some _) => False
  | _ => True

/-- An auxiliary node can name one unresolved parent. An auxiliary PRF
query names its stream key. Resolved logical nodes use their protocol budget
instead; their known-parent references are covered by the shared collision
event when compared with another node's digest. -/
def claims {T : Type} : Name P T → Finset Digest
  | .inl (_,some _) => ∅
  | .inl (point,none) => match Strand.Input.decode (bytes point) with
      | some (.node _ [digest] _) => {digest}
      | _ => ∅
  | .inr digest => {digest.2}

omit [DecidableEq P] in
theorem claims_card {T : Type} (point : Name P T) :
    (claims bytes point).card ≤ if auxiliary point then 1 else 0 := by
  cases point with
  | inr digest => simp [claims,auxiliary]
  | inl point =>
      rcases point with ⟨point,logical⟩
      cases logical with
      | some logical => simp [claims,auxiliary]
      | none =>
          simp only [claims,auxiliary,if_true]
          split <;> simp

section Streams
variable {fuel : ℕ} (program : Tree (Point P PrfKey Word) Digest Out fuel)
variable (H : Name P T → Sample Digest Word) (G : Point P PrfKey Word → Digest)
local notation "tree" => searchState schema bytes program Cache.empty []

/-- On an uncharged, collision-free execution, a sampled node's challenge
row is precisely its reserved raw PRF row. If a PRF prequery had already
reserved that row, freshness would place it before the node; the no-guess
condition would place it after the node. Thus it cannot be silently treated
as a fresh independent challenge. -/
theorem node_stream
    (agreement : ((tree).run H).1.1.2.Matches G)
    (collisionFree : ∀ a, (.inl a : Raw) ∈ Bcs.TotalOracle.queried program G →
      ∀ b, (.inl b : Raw) ∈ Bcs.TotalOracle.queried program G → G (.inl a) = G (.inl b) → a = b)
    (noGuess : ¬DigestProjection.Guess (claims bytes) tree H)
    (raw : P) (logical : Option T) (answer : Answer)
    (member : ((.inl (raw,logical),answer) : Name P T × Answer) ∈ ((tree).run H).2) :
    ∀ counter, G (.inr (key bytes raw answer.1,counter)) = answer.2 counter := by
  have cached := searchState_node_cached schema bytes program Cache.empty [] H raw logical answer member
  have reserved := searchState_reserved schema bytes program Cache.empty [] H (Cache.reserved_empty (key bytes))
  obtain ⟨row,known⟩ := reserved raw answer.1 cached
  have sameRow : row = answer.2 := by
    obtain ⟨source,result,sourceQuery,sameKey,rowEq⟩ :=
      searchState_stream_origin schema bytes program H (key bytes raw answer.1) row known
    cases source with
    | inl source =>
        rcases source with ⟨other,decoded⟩
        have sameDigest : result.1 = answer.1 := congrArg Prod.snd sameKey
        have answers := (searchState_source schema bytes program Cache.empty [] H G agreement).2
        have same := collisionFree other
          (searchState_node_queried schema bytes program Cache.empty [] H G agreement other decoded result sourceQuery)
          raw (searchState_node_queried schema bytes program Cache.empty [] H G agreement raw logical answer member)
          ((answers other decoded result sourceQuery).trans (sameDigest.trans (answers raw logical answer member).symm))
        subst other
        have values := searchState_answers_eq schema bytes program Cache.empty [] H
          (.inl (raw,decoded)) (.inl (raw,logical)) result answer sourceQuery member rfl
        exact rowEq.symm.trans (congrArg Prod.snd values)
    | inr digest =>
        exfalso
        change digest = key bytes raw answer.1 at sameKey
        have node : (.inl (raw,logical) : Name P T) ∈ seen tree H :=
          List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) member)
        have stream : (.inr digest : Name P T) ∈ seen tree H :=
          List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) sourceQuery)
        have claimed : (H (.inl (raw,logical))).1 ∈ claims bytes (.inr digest : Name P T) := by
          rw [← Tree.trace_sound tree H _ member]
          exact mem_singleton.mpr (congrArg Prod.snd sameKey.symm)
        have earlier := DigestProjection.parent_before_child (claims bytes) tree H noGuess _ _ node stream claimed
        obtain ⟨first,rest,current,splitTrace,past⟩ := trace_split_before tree H (.inr digest) stream
        rw [← past] at earlier
        obtain ⟨⟨point,value⟩,inFirst,equal⟩ := List.mem_map.mp earlier
        change point = .inl (raw,logical) at equal
        subst point
        have ordered := searchState_fresh_streams schema bytes program Cache.empty [] H
        simp only [FreshStreams,splitTrace,List.map_append,List.map_cons] at ordered
        have distinct := (List.pairwise_append.mp ordered).2.2
          _ (List.mem_map_of_mem (f := fun qa : Name P T × Answer => (erase qa.1,qa.2)) inFirst)
          _ List.mem_cons_self
        change key bytes raw value.1 ≠ digest at distinct
        have earlierQuery : ((.inl (raw,logical),value) : Name P T × Answer) ∈ ((tree).run H).2 := by
          rw [splitTrace]
          exact List.mem_append_left _ inFirst
        have equalValue := (Tree.trace_sound tree H _ earlierQuery).trans (Tree.trace_sound tree H _ member).symm
        exact distinct ((congrArg (key bytes raw) (congrArg Prod.fst equalValue)).trans sameKey.symm)
  intro counter
  rw [← sameRow]
  exact agreement.2 (key bytes raw answer.1) row known counter

end Streams

def speculation {fuel : ℕ} (program : Tree Raw Digest Out fuel) (H : Name P T → Answer) : ℚ :=
  DigestProjection.charge (claims bytes) (search schema bytes program) H

theorem speculation_nonneg {fuel : ℕ} (program : Tree Raw Digest Out fuel) (H : Name P T → Answer) :
    0 ≤ speculation schema bytes program H :=
  DigestProjection.charge_nonneg (claims bytes) (search schema bytes program) H

/-- The strand's speculative allowance is established independently of all
protocol charges. This is the averaging obligation consumed by the generic
soundness realization, with one planted target per auxiliary query. -/
theorem search_speculation_le [Fintype P] [Fintype T]
    {fuel : ℕ} (program : Tree Raw Digest Out fuel) (epsilon : ℚ)
    (guessFits : (fuel : ℚ)/Fintype.card Digest ≤ epsilon) :
    (∑ H, speculation schema bytes program H) ≤
      ∑ H : Name P T → Answer, ∑ point ∈ seen (search schema bytes program) H,
        if auxiliary point then epsilon else 0 :=
  StrandCharging.targets_sum_le (search schema bytes program) (seen_card_le _)
    auxiliary (claims bytes) (claims_card bytes) epsilon
    (by simpa only [Nat.cast_one,mul_one] using guessFits)

/-- The concrete query classification consumes only the source program's
SHA-query budget. Local algebraic bounds are still required, but neither
the decoder nor speculative queries create a second global budget. -/
theorem search_charges_le [Fintype P] [Fintype T]
    {fuel : ℕ} (program : Tree Raw Digest Out fuel)
    (protocol : (Name P T → Answer) → ℚ) (epsilon : ℚ) (positive : 0 ≤ epsilon)
    (protocolMean : (∑ H, protocol H) ≤ ∑ H : Name P T → Answer,
      ∑ p ∈ seen (search schema bytes program) H,
        if auxiliary p then 0 else epsilon)
    (guessFits : (fuel : ℚ)/Fintype.card Digest ≤ epsilon) :
    (∑ H : Name P T → Answer, (protocol H +
      ∑ p ∈ seen (search schema bytes program) H,
        if DigestProjection.bad (claims bytes)
          (search schema bytes program) p H (H p) then 1 else 0)) ≤
      (fuel : ℚ)*epsilon*(Fintype.card Answer : ℚ)^Fintype.card (Name P T) := by
  exact StrandCharging.shared_targets_sum_le (search schema bytes program)
    (seen_card_le _) auxiliary (claims bytes) (claims_card bytes) protocol epsilon positive
    protocolMean (by simpa only [Nat.cast_one,mul_one] using guessFits)

end LfzkV2.Current.StrandSearch
