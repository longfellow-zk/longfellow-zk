import LfzkV2.Current.StrandRecognition

/-! Recover an accepted path from the recorded raw search and verifier replay.
The replay uses the search's actual cache. Node visibility, answer agreement
and the source of the final PRF stream are derived from those executions;
they are not additional certificates supplied to the verifier. -/
noncomputable section
namespace LfzkV2.Current.StrandReplay
open Finset Merkle.RandomOracle TranscriptV2
open TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T Out Result : Type} [DecidableEq P]
variable (schema : History.Codec T) (bytes : P → Framing.Bytes)
variable {fuel extra rounds : ℕ}
variable (program : Tree (Point P PrfKey Word) Digest Out fuel)
variable (replay : Out → Tree (Point P PrfKey Word) Digest Result extra)

local notation "Name" => StrandSearch.Name P T
local notation "Answer" => Sample Digest Word

/-- The extraction cut retains both raw observations and the two caches.
Later replay can extend these caches but cannot replace their answers. -/
abbrev Cut (P Out : Type) :=
  ((Out × List (Point P PrfKey Word × Digest)) × Cache P PrfKey Digest Word) × List Entry

def search : Tree Name Answer (Cut P Out) fuel :=
  StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []

def resume (cut : Cut P Out) : Tree Name Answer (Cut P Result) extra :=
  StrandSearch.searchState schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2

local notation "tree" => search schema bytes program
local notation "finish" => resume schema bytes replay

/-- Verifier continuation preserves the cache at proof submission. -/
theorem original_matches (H : Name → Answer) (G : Point P PrfKey Word → Digest)
    (agreement : ((((tree).bind finish).run H).1).1.2.Matches G) :
    ((tree).run H).1.1.2.Matches G := by
  let cut := ((tree).run H).1
  have final : ((finish cut).run H).1.1.2.Matches G := by
    simpa only [Tree.run_bind,cut] using agreement
  exact Cache.Matches.of_extension
    (StrandSearch.searchState_extends schema bytes (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2 H) final

omit replay in
/-- A raw node queried before proof submission has a named source in that
same original search. Repeated queries use their first recorded source. -/
theorem original_node_origin (H : Name → Answer) (G : Point P PrfKey Word → Digest)
    (agreement : ((tree).run H).1.1.2.Matches G) (raw : P)
    (queried : (.inl raw : Point P PrfKey Word) ∈ seen program G) :
    ∃ logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ ((tree).run H).2 := by
  have source := StrandSearch.searchState_source schema bytes (recordTrace program) Cache.empty [] H G agreement
  have actualTrace : (program.run G).2 = ((tree).run H).1.1.1.2 := by
    change (program.run G).2 =
      ((StrandSearch.searchState schema bytes (recordTrace program) Cache.empty []).run H).1.1.1.2
    exact congrArg Prod.snd (by simpa only [run_recordTrace] using source.1)
  obtain ⟨⟨point,digest⟩,member,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
  change point = .inl raw at equal
  subst point
  rw [actualTrace] at member
  have cached := StrandSearch.searchState_raw_covered schema bytes program Cache.empty [] H _ _ member
  obtain ⟨logical,answer,present,_⟩ := StrandSearch.searchState_node_origin schema bytes (recordTrace program) H raw digest cached
  exact ⟨logical,answer,present⟩

/-- A completed replay cache extends the original search cache, so every
node answer in that search is still the actual raw digest. -/
theorem node_answer (H : Name → Answer) (G : Point P PrfKey Word → Digest)
    (agreement : ((((tree).bind finish).run H).1).1.2.Matches G)
    (raw : P) (logical : Option T) (answer : Answer)
    (member : ((.inl (raw,logical),answer) : Name × Answer) ∈ ((tree).run H).2) :
    G (.inl raw) = answer.1 := by
  let cut := ((tree).run H).1
  have extended := StrandSearch.searchState_extends schema bytes
    (recordTrace (replay cut.1.1.1)) cut.1.2 cut.2 H
  have final : ((finish cut).run H).1.1.2.Matches G := by
    simpa only [Tree.run_bind,cut] using agreement
  have early : cut.1.2.Matches G := Cache.Matches.of_extension extended final
  exact (StrandSearch.searchState_source schema bytes (recordTrace program) Cache.empty []
    H G early).2 raw logical answer member

/-- Named node observations and actual raw calls agree throughout the
search and authentication replay. Cached repeats still have one original
named source; replay does not invent new commitment evidence. -/
theorem node_observations (H : Name → Answer) (G : Point P PrfKey Word → Digest)
    (agreement : ((((tree).bind finish).run H).1).1.2.Matches G) :
    (∀ raw logical answer,
      ((.inl (raw,logical),answer) : Name × Answer) ∈ (((tree).bind finish).run H).2 →
      G (.inl raw) = answer.1 ∧ (.inl raw : Point P PrfKey Word) ∈ seen (program.bind replay) G) ∧
    (∀ raw, (.inl raw : Point P PrfKey Word) ∈ seen (program.bind replay) G →
      ∃ logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (((tree).bind finish).run H).2) := by
  let joined := (recordTrace program).bind fun cut => recordTrace (replay cut.1)
  have joinedRun : (StrandSearch.searchState schema bytes joined Cache.empty []).run H =
      ((tree).bind finish).run H := StrandSearch.searchState_bind schema bytes _ _ _ _ H
  have joinedMatches : ((StrandSearch.searchState schema bytes joined Cache.empty []).run H).1.1.2.Matches G := by
    rw [joinedRun]
    exact agreement
  have queried raw : raw ∈ Bcs.TotalOracle.queried joined G ↔ raw ∈ seen (program.bind replay) G := by
    simp only [joined,Bcs.TotalOracle.queried,Tree.run_bind,run_recordTrace,seen,
      List.map_append,List.mem_append,List.mem_toFinset]
  constructor
  · intro raw logical answer member
    have named : ((.inl (raw,logical),answer) : Name × Answer) ∈
        ((StrandSearch.searchState schema bytes joined Cache.empty []).run H).2 := by
      rw [joinedRun]
      exact member
    exact ⟨(StrandSearch.searchState_source schema bytes joined Cache.empty [] H G joinedMatches).2
        raw logical answer named,
      (queried _).mp (StrandSearch.searchState_node_queried schema bytes joined Cache.empty [] H G joinedMatches
        raw logical answer named)⟩
  · intro raw member
    let cut := ((tree).run H).1
    have finalMatches : ((finish cut).run H).1.1.2.Matches G := by
      simpa only [Tree.run_bind,cut] using agreement
    obtain ⟨first,last⟩ := StrandSearch.replay_source schema bytes program replay H G finalMatches
    obtain ⟨⟨point,digest⟩,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    change point = .inl raw at same
    subst point
    rw [Tree.run_bind] at present
    have cached : ((finish cut).run H).1.1.2.nodes raw = some digest := by
      rcases List.mem_append.mp present with early | late
      · rw [first] at early
        have atCut := StrandSearch.searchState_raw_covered schema bytes program Cache.empty [] H (.inl raw) digest early
        exact (StrandSearch.searchState_extends schema bytes (recordTrace (replay cut.1.1.1))
          cut.1.2 cut.2 H).1 raw digest atCut
      · rw [last] at late
        exact StrandSearch.searchState_raw_covered schema bytes (replay cut.1.1.1)
          cut.1.2 cut.2 H (.inl raw) digest late
    have atJoined : ((StrandSearch.searchState schema bytes joined Cache.empty []).run H).1.1.2.nodes raw = some digest := by
      rw [joinedRun,Tree.run_bind]
      exact cached
    obtain ⟨logical,answer,origin,_⟩ := StrandSearch.searchState_node_origin schema bytes joined H raw digest atJoined
    rw [joinedRun] at origin
    exact ⟨logical,answer,origin⟩

/-- Replaying an uncharged execution cannot substitute a previously
reserved PRF row for a node's independent sampled answer. The same explicit
guess and collision exceptions used for path recovery suffice for this
stronger, byte-for-byte challenge correspondence. -/
theorem node_stream (H : Name → Answer) (G : Point P PrfKey Word → Digest)
    (agreement : ((((tree).bind finish).run H).1).1.2.Matches G)
    (collisionFree : ∀ a, (.inl a : Point P PrfKey Word) ∈ seen (program.bind replay) G →
      ∀ b, (.inl b : Point P PrfKey Word) ∈ seen (program.bind replay) G →
      G (.inl a) = G (.inl b) → a = b)
    (noReplayHit : ¬∃ point, DigestProjection.Replay.bad (StrandSearch.claims bytes)
      tree finish point H (H point))
    (uncharged : ¬1 ≤ DigestProjection.charge (StrandSearch.claims bytes) tree H)
    (raw : P) (logical : Option T) (answer : Answer)
    (member : ((.inl (raw,logical),answer) : Name × Answer) ∈ (((tree).bind finish).run H).2) :
    ∀ counter, G (.inr (StrandSearch.key bytes raw answer.1,counter)) = answer.2 counter := by
  let joined := (recordTrace program).bind fun cut => recordTrace (replay cut.1)
  have joinedRun : (StrandSearch.searchState schema bytes joined Cache.empty []).run H =
      ((tree).bind finish).run H := StrandSearch.searchState_bind schema bytes _ _ _ _ H
  have joinedMatches : ((StrandSearch.searchState schema bytes joined Cache.empty []).run H).1.1.2.Matches G := by
    rw [joinedRun]
    exact agreement
  have queried raw : raw ∈ Bcs.TotalOracle.queried joined G ↔ raw ∈ seen (program.bind replay) G := by
    simp only [joined,Bcs.TotalOracle.queried,Tree.run_bind,run_recordTrace,seen,
      List.map_append,List.mem_append,List.mem_toFinset]
  have noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) ((tree).bind finish) H := by
    intro hit
    rcases DigestProjection.Replay.guess_split (StrandSearch.claims bytes) tree finish H hit with early | late
    · exact uncharged (DigestProjection.guess_charged (StrandSearch.claims bytes) tree H early)
    · exact noReplayHit late
  have sameTrace : ((StrandSearch.searchState schema bytes joined Cache.empty []).run H).2 =
      (((tree).bind finish).run H).2 := congrArg Prod.snd joinedRun
  have sameBefore := before_eq_of_queried_eq (StrandSearch.searchState schema bytes joined Cache.empty [])
    ((tree).bind finish) H H (congrArg (List.map Prod.fst) sameTrace)
  apply StrandSearch.node_stream schema bytes joined H G joinedMatches
    (fun a ha b hb same => collisionFree a ((queried _).mp ha) b ((queried _).mp hb) same) ?_ raw logical answer ?_
  · simpa only [DigestProjection.Guess,DigestCharging.targets,sameBefore,
      seen,Bcs.TotalOracle.queried,sameTrace] using noGuess
  · rw [sameTrace]
    exact member

end LfzkV2.Current.StrandReplay
