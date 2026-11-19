import TranscriptV2.StrandTrace

/-! Identify which actual query first supplied each cached digest or PRF row.
This complements cache coverage: a row available at proof submission comes
from a node query or an early PRF query in that search, never from verifier
replay or an independently chosen replacement answer. -/
namespace TranscriptV2.StrandCoupling
open Merkle.RandomOracle

variable {P K D I Out : Type}
variable (nodeKey : P → D → K)

/-- Node queries reserve the row addressed by their answer. Early PRF
queries reserve the row addressed by their input, not their dummy digest. -/
def streamKey : SamplePoint P K → Sample D I → K
  | .inl point,answer => nodeKey point answer.1
  | .inr digest,_ => digest

structure Cache.Source (initial : Cache P K D I)
    (trace : List (SamplePoint P K × Sample D I)) (current : Cache P K D I) : Prop where
  nodes : ∀ point digest, current.nodes point = some digest →
    initial.nodes point = some digest ∨
      ∃ answer, ((.inl point,answer) : SamplePoint P K × Sample D I) ∈ trace ∧ answer.1 = digest
  streams : ∀ digest bytes, current.streams digest = some bytes →
    initial.streams digest = some bytes ∨
      ∃ point answer, (point,answer) ∈ trace ∧ streamKey nodeKey point answer = digest ∧ answer.2 = bytes

theorem Cache.Source.refl {nodeKey : P → D → K} (state : Cache P K D I) : state.Source nodeKey [] state :=
  ⟨fun _ _ found => Or.inl found,fun _ _ found => Or.inl found⟩

theorem Cache.Source.mono {nodeKey : P → D → K} {initial current : Cache P K D I}
    {first second : List (SamplePoint P K × Sample D I)}
    (source : initial.Source nodeKey first current) (subset : first ⊆ second) :
    initial.Source nodeKey second current := by
  constructor
  · intro point digest found
    rcases source.nodes point digest found with old | ⟨answer,member,same⟩
    · exact Or.inl old
    · exact Or.inr ⟨answer,subset member,same⟩
  · intro digest bytes found
    rcases source.streams digest bytes found with old | ⟨point,answer,member,key,row⟩
    · exact Or.inl old
    · exact Or.inr ⟨point,answer,subset member,key,row⟩

theorem Cache.Source.trans {nodeKey : P → D → K} {initial middle final : Cache P K D I}
    {first second : List (SamplePoint P K × Sample D I)}
    (left : initial.Source nodeKey first middle) (right : middle.Source nodeKey second final) :
    initial.Source nodeKey (first ++ second) final := by
  have earlier := left.mono (fun _ member => List.mem_append_left second member)
  have later := right.mono (fun _ member => List.mem_append_right first member)
  constructor
  · intro point digest found
    exact (later.nodes point digest found).elim (earlier.nodes point digest) Or.inr
  · intro digest bytes found
    exact (later.streams digest bytes found).elim (earlier.streams digest bytes) Or.inr

variable [DecidableEq P] [DecidableEq K]

omit [DecidableEq K] in
theorem Cache.Source.node {nodeKey : P → D → K} {initial current : Cache P K D I}
    {trace : List (SamplePoint P K × Sample D I)} (source : initial.Source nodeKey trace current)
    (point : P) (answer : Sample D I) (member : ((.inl point,answer) : SamplePoint P K × Sample D I) ∈ trace) :
    initial.Source nodeKey trace (current.node point answer.1) := by
  constructor
  · intro other digest found
    by_cases same : other = point
    · subst other
      have equal : answer.1 = digest := by simpa only [Cache.node,Function.update_self,Option.some.injEq] using found
      exact Or.inr ⟨answer,member,equal⟩
    · exact source.nodes other digest (by simpa only [Cache.node,Function.update_of_ne same] using found)
  · exact source.streams

omit [DecidableEq P] in
theorem Cache.Source.stream {nodeKey : P → D → K} {initial current : Cache P K D I}
    {trace : List (SamplePoint P K × Sample D I)} (source : initial.Source nodeKey trace current)
    (point : SamplePoint P K) (answer : Sample D I) (member : (point,answer) ∈ trace) :
    initial.Source nodeKey trace (current.stream (streamKey nodeKey point answer) answer.2) := by
  constructor
  · exact source.nodes
  · intro digest bytes found
    by_cases same : digest = streamKey nodeKey point answer
    · subst digest
      have equal : answer.2 = bytes := by simpa only [Cache.stream,Function.update_self,Option.some.injEq] using found
      exact Or.inr ⟨point,answer,member,rfl,equal⟩
    · exact source.streams digest bytes (by simpa only [Cache.stream,Function.update_of_ne same] using found)

/-- Cache origins are derived from the actual execution. In particular a
prequeried row remains attributed to that earlier PRF query when a later node
hash happens to reach its digest. -/
theorem eagerState_source_queries {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    state.Source nodeKey ((eagerState nodeKey program state).run H).2 ((eagerState nodeKey program state).run H).1.2 := by
  induction program generalizing state with
  | done output => exact Cache.Source.refl state
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simpa only [eagerState,found,Tree.run_weaken] using ih digest state
          | none =>
              let answer := H (.inl point)
              have initial : state.Source nodeKey [(.inl point,answer)] state :=
                (Cache.Source.refl state).mono (fun _ member => nomatch member)
              have node := initial.node point answer List.mem_cons_self
              cases row : state.streams (nodeKey point answer.1) with
              | some bytes =>
                  simpa only [eagerState,found,Tree.run_query,show H (.inl point) = answer from rfl,
                    row,List.singleton_append] using node.trans (ih answer.1 _)
              | none =>
                  simpa only [eagerState,found,Tree.run_query,show H (.inl point) = answer from rfl,
                    row,List.singleton_append,streamKey] using
                    (node.stream (.inl point) answer List.mem_cons_self).trans (ih answer.1 _)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simpa only [eagerState,found,Tree.run_weaken] using ih (bytes counter) state
          | none =>
              let answer := H (.inr digest)
              have initial : state.Source nodeKey [(.inr digest,answer)] state :=
                (Cache.Source.refl state).mono (fun _ member => nomatch member)
              simpa only [eagerState,found,Tree.run_query,List.singleton_append,streamKey,answer] using
                (initial.stream (.inr digest) answer List.mem_cons_self).trans (ih (answer.2 counter) _)

/-- A fresh PRF query cannot follow an earlier reservation of its row.
Node queries with equal digests may share a row; that separate possibility
is handled by the actual SHA collision event. -/
def FreshStreams (trace : List (SamplePoint P K × Sample D I)) : Prop :=
  trace.Pairwise fun earlier later => match later.1 with
    | .inl _ => True
    | .inr digest => streamKey nodeKey earlier.1 earlier.2 ≠ digest

omit [DecidableEq P] [DecidableEq K] in
private theorem freshStreams_cons {fuel : ℕ}
    (current : SamplePoint P K × Sample D I) (state : Cache P K D I)
    (tree : Tree (SamplePoint P K) (Sample D I) Out fuel) (H : SamplePoint P K → Sample D I)
    (fresh : FreshOracle.FreshFrom state.known tree)
    (known : state.known (.inr (streamKey nodeKey current.1 current.2)))
    (later : FreshStreams nodeKey (tree.run H).2) : FreshStreams nodeKey (current :: (tree.run H).2) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_,later⟩
  rintro ⟨point,answer⟩ member
  cases point with
  | inl point => trivial
  | inr digest =>
      intro same
      apply fresh.not_queried H (.inr digest) (same ▸ known)
      exact List.mem_map_of_mem (f := Prod.fst) member

theorem eagerState_fresh_streams {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    FreshStreams nodeKey ((eagerState nodeKey program state).run H).2 := by
  induction program generalizing state with
  | done output => exact .nil
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simpa only [eagerState,found,Tree.run_weaken] using ih digest state
          | none =>
              cases row : state.streams (nodeKey point (H (.inl point)).1) with
              | some bytes =>
                  simp only [eagerState,found,Tree.run_query,row]
                  apply freshStreams_cons nodeKey _ _ _ H (eagerState_fresh nodeKey _ _) _ (ih _ _)
                  simp only [streamKey,Cache.known,Cache.node,row,Option.isSome_some]
              | none =>
                  simp only [eagerState,found,Tree.run_query,row]
                  apply freshStreams_cons nodeKey _ _ _ H (eagerState_fresh nodeKey _ _) _ (ih _ _)
                  simp only [streamKey,Cache.known,Cache.stream,Function.update_self,Option.isSome_some]
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simpa only [eagerState,found,Tree.run_weaken] using ih (bytes counter) state
          | none =>
              simp only [eagerState,found,Tree.run_query]
              apply freshStreams_cons nodeKey _ _ _ H (eagerState_fresh nodeKey _ _) _ (ih _ _)
              simp only [streamKey,Cache.known,Cache.stream,Function.update_self,Option.isSome_some]

/-- Every sampled node answer is retained in the final cache. This is
stronger than merely saying that every cached answer has a query source. -/
theorem eagerState_node_cached {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I)
    (point : P) (answer : Sample D I)
    (member : ((.inl point,answer) : SamplePoint P K × Sample D I) ∈ ((eagerState nodeKey program state).run H).2) :
    ((eagerState nodeKey program state).run H).1.2.nodes point = some answer.1 := by
  induction program generalizing state with
  | done output => cases member
  | query raw next ih =>
      cases raw with
      | inl raw =>
          cases found : state.nodes raw with
          | some digest =>
              simp only [eagerState,found,Tree.run_weaken] at member ⊢
              exact ih digest state member
          | none =>
              let after := match state.streams (nodeKey raw (H (.inl raw)).1) with
                | some _ => state.node raw (H (.inl raw)).1
                | none => (state.node raw (H (.inl raw)).1).stream (nodeKey raw (H (.inl raw)).1) (H (.inl raw)).2
              simp only [eagerState,found,Tree.run_query] at member ⊢
              change ((.inl point,answer) : SamplePoint P K × Sample D I) ∈
                (.inl raw,H (.inl raw)) :: ((eagerState nodeKey (next (H (.inl raw)).1) after).run H).2 at member
              change ((eagerState nodeKey (next (H (.inl raw)).1) after).run H).1.2.nodes point = some answer.1
              rcases List.mem_cons.mp member with current | later
              · obtain ⟨same,value⟩ := Prod.mk.inj current
                cases Sum.inl.inj same
                cases value
                apply (eagerState_extends nodeKey _ after H).1
                dsimp only [after]
                split <;> exact Function.update_self _ _ _
              · exact ih _ after later
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes =>
              simp only [eagerState,found,Tree.run_weaken] at member ⊢
              exact ih _ state member
          | none =>
              simp only [eagerState,found,Tree.run_query] at member ⊢
              rcases List.mem_cons.mp member with impossible | later
              · cases Prod.mk.inj impossible |>.1
              · exact ih _ _ later

end TranscriptV2.StrandCoupling
