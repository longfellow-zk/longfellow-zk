import TranscriptV2.Queries
import TranscriptV2.StrandReplay

/-! A coupled run describes one consistent raw SHA execution. The sampling
cache only grows, so its final contents reproduce both the source output and
every recorded node answer, including after prequeries and hash collisions. -/
namespace TranscriptV2.StrandCoupling
open Merkle.RandomOracle Bcs.TotalOracle

variable {P K D I Out : Type}

def Cache.Extends (earlier later : Cache P K D I) : Prop :=
  (∀ point digest, earlier.nodes point = some digest → later.nodes point = some digest) ∧
    (∀ digest bytes, earlier.streams digest = some bytes → later.streams digest = some bytes)

theorem Cache.Extends.refl (state : Cache P K D I) : state.Extends state :=
  ⟨fun _ _ h => h,fun _ _ h => h⟩

theorem Cache.Extends.trans {first second third : Cache P K D I}
    (left : first.Extends second) (right : second.Extends third) : first.Extends third :=
  ⟨fun point digest h => right.1 point digest (left.1 point digest h),
    fun digest bytes h => right.2 digest bytes (left.2 digest bytes h)⟩

theorem Cache.node_extends [DecidableEq P] (state : Cache P K D I) (point : P) (digest : D)
    (fresh : state.nodes point = none) : state.Extends (state.node point digest) := by
  refine ⟨?_,fun _ _ h => h⟩
  intro other answer found
  by_cases same : other = point
  · subst other
    rw [fresh] at found
    cases found
  · simpa only [Cache.node,Function.update_of_ne same] using found

theorem Cache.stream_extends [DecidableEq K] (state : Cache P K D I) (digest : K) (bytes : Stream D I)
    (fresh : state.streams digest = none) : state.Extends (state.stream digest bytes) := by
  refine ⟨fun _ _ h => h,?_⟩
  intro other answer found
  by_cases same : other = digest
  · subst other
    rw [fresh] at found
    cases found
  · simpa only [Cache.stream,Function.update_of_ne same] using found

def Cache.Matches (state : Cache P K D I) (oracle : Point P K I → D) : Prop :=
  (∀ point digest, state.nodes point = some digest → oracle (.inl point) = digest) ∧
    (∀ digest bytes, state.streams digest = some bytes → ∀ counter, oracle (.inr (digest,counter)) = bytes counter)

theorem Cache.Matches.of_extension {earlier later : Cache P K D I} {oracle : Point P K I → D}
    (extension : earlier.Extends later) (agreement : later.Matches oracle) : earlier.Matches oracle :=
  ⟨fun point digest h => agreement.1 point digest (extension.1 point digest h),
    fun digest bytes h => agreement.2 digest bytes (extension.2 digest bytes h)⟩

def Cache.raw (state : Cache P K D I) (fallback : D) : Point P K I → D
  | .inl point => (state.nodes point).getD fallback
  | .inr (digest,counter) => ((state.streams digest).getD (fun _ => fallback)) counter

theorem Cache.matches_raw (state : Cache P K D I) (fallback : D) : state.Matches (state.raw fallback) := by
  constructor
  · intro point digest found
    simp only [raw,found,Option.getD_some]
  · intro digest bytes found counter
    simp only [raw,found,Option.getD_some]

/-- The cache stores all observed raw blocks, even when grouping a PRF row
removed their individual queries from the transformed execution's trace. -/
def Cache.lookup (state : Cache P K D I) : Point P K I → Option D
  | .inl point => state.nodes point
  | .inr (digest,counter) => (state.streams digest).map fun bytes => bytes counter

theorem Cache.matches_iff_lookup (state : Cache P K D I) (G : Point P K I → D) :
    state.Matches G ↔ ∀ point answer, state.lookup point = some answer → G point = answer := by
  constructor
  · intro agreement point answer found
    cases point with
    | inl point => exact agreement.1 point answer found
    | inr address =>
        rcases address with ⟨digest,counter⟩
        obtain ⟨bytes,known,same⟩ := Option.map_eq_some_iff.mp found
        exact (agreement.2 digest bytes known counter).trans same
  · intro agreement
    constructor
    · intro point answer found
      exact agreement (.inl point) answer found
    · intro digest bytes found counter
      exact agreement (.inr (digest,counter)) (bytes counter)
        (by simp only [lookup,found,Option.map_some])

theorem Cache.Matches.update [DecidableEq (Point P K I)] {state : Cache P K D I}
    {G : Point P K I → D} (agreement : state.Matches G) (point : Point P K I)
    (missing : state.lookup point = none) (answer : D) :
    state.Matches (Function.update G point answer) := by
  apply (Cache.matches_iff_lookup _ _).mpr
  intro other value found
  have different : other ≠ point := by
    intro same
    subst other
    rw [missing] at found
    cases found
  rw [Function.update_of_ne different]
  exact (Cache.matches_iff_lookup _ _).mp agreement other value found

variable [DecidableEq P] [DecidableEq K]
variable (streamKey : P → D → K)

omit [DecidableEq P] [DecidableEq K] in
/-- Eager sampling reserves every node's whole counter stream. Later
sampler reads therefore add no fresh coordinate, even after rejection. -/
def Cache.Reserved (state : Cache P K D I) : Prop :=
  ∀ point digest, state.nodes point = some digest → ∃ row, state.streams (streamKey point digest) = some row

omit [DecidableEq P] [DecidableEq K] in
theorem Cache.reserved_empty : (Cache.empty : Cache P K D I).Reserved streamKey :=
  fun _ _ found => nomatch found

omit [DecidableEq K] in
theorem Cache.Reserved.node {state : Cache P K D I} (reserved : state.Reserved streamKey)
    (point : P) (digest : D) (row : Stream D I) (known : state.streams (streamKey point digest) = some row) :
    (state.node point digest).Reserved streamKey := by
  intro other value found
  by_cases same : other = point
  · subst other
    have equal : digest = value := by simpa only [Cache.node,Function.update_self,Option.some.injEq] using found
    exact equal ▸ ⟨row,known⟩
  · exact reserved other value (by simpa only [Cache.node,Function.update_of_ne same] using found)

omit [DecidableEq P] in
theorem Cache.Reserved.stream {state : Cache P K D I} (reserved : state.Reserved streamKey)
    (digest : K) (row : Stream D I) : (state.stream digest row).Reserved streamKey := by
  intro point value found
  obtain ⟨earlier,known⟩ := reserved point value found
  by_cases same : streamKey point value = digest
  · exact ⟨row,by simp only [Cache.stream,same,Function.update_self]⟩
  · exact ⟨earlier,by simpa only [Cache.stream,Function.update_of_ne same] using known⟩

theorem Cache.Reserved.new_node {state : Cache P K D I} (reserved : state.Reserved streamKey)
    (point : P) (digest : D) (row : Stream D I) :
    ((state.node point digest).stream (streamKey point digest) row).Reserved streamKey := by
  have reordered : (state.node point digest).stream (streamKey point digest) row =
      (state.stream (streamKey point digest) row).node point digest := rfl
  rw [reordered]
  exact Cache.Reserved.node streamKey
    (Cache.Reserved.stream streamKey reserved (streamKey point digest) row)
    point digest row (by simp only [Cache.stream,Function.update_self])

/-- The reservation invariant holds after arbitrary adversarial queries,
including PRF prequeries. It is not an honest-query-order assumption. -/
theorem eagerState_reserved {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) (reserved : state.Reserved streamKey) :
    ((eagerState streamKey program state).run H).1.2.Reserved streamKey := by
  induction program generalizing state with
  | done output => exact reserved
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simpa only [eagerState,found,Tree.run_weaken] using ih digest state reserved
          | none =>
              simp only [eagerState,found,Tree.run_query]
              cases row : state.streams (streamKey point (H (.inl point)).1) with
              | some bytes => exact ih _ _ (Cache.Reserved.node streamKey reserved point _ bytes row)
              | none => exact ih _ _ (Cache.Reserved.new_node streamKey reserved point _ _)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simpa only [eagerState,found,Tree.run_weaken] using ih (bytes counter) state reserved
          | none =>
              simp only [eagerState,found,Tree.run_query]
              exact ih _ _ (Cache.Reserved.stream streamKey reserved digest _)

/-- Once a row is reserved, arbitrary reads of that row retain its bytes
and produce no new sample query. This includes repeated and rejected draws. -/
theorem eagerState_stream {fuel : ℕ} (program : Tree I D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I)
    (digest : K) (row : Stream D I) (known : state.streams digest = some row) :
    (eagerState streamKey (mapQueries (fun counter => (.inr (digest,counter) : Point P K I)) program) state).run H =
      (((program.run row).1,state),[]) := by
  induction program with
  | done output => rfl
  | query counter next ih =>
      simpa only [mapQueries,eagerState,known,Tree.run_weaken,Tree.run_query] using ih (row counter)

/-- One boundary spends at most one new sample coordinate. The node hash
reserves its row before the sampler starts; a cached node already has a row.
This bound is independent of the number of raw counter-block reads. -/
theorem eagerState_round_length {fuel : ℕ} (point : P) (program : D → Tree I D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) (reserved : state.Reserved streamKey) :
    ((eagerState streamKey (.query (.inl point) fun digest =>
      mapQueries (fun counter => (.inr (streamKey point digest,counter) : Point P K I)) (program digest)) state).run H).2.length ≤ 1 := by
  cases found : state.nodes point with
  | some digest =>
      obtain ⟨row,known⟩ := reserved point digest found
      simp only [eagerState,found,Tree.run_weaken,eagerState_stream streamKey (program digest) state H (streamKey point digest) row known,List.length_nil,Nat.zero_le]
  | none =>
      simp only [eagerState,found,Tree.run_query,List.length_cons]
      cases row : state.streams (streamKey point (H (.inl point)).1) with
      | some bytes =>
          dsimp only
          rw [eagerState_stream streamKey (program (H (.inl point)).1) (state.node point (H (.inl point)).1) H _ bytes row]
          exact le_rfl
      | none =>
          dsimp only
          rw [eagerState_stream streamKey (program (H (.inl point)).1) _ H _ (H (.inl point)).2
            (by simp only [Cache.stream,Function.update_self])]
          exact le_rfl

/-- Expanding a logical replay retains the sum of its per-boundary sample
budgets. Raw sampler fuel never substitutes for this distinct-row budget. -/
theorem eagerState_expand_length {Logical A : Type} {rounds blocks cost : ℕ}
    (read : Logical → Tree (Point P K I) D A blocks)
    (bounded : ∀ point state H, state.Reserved streamKey →
      ((eagerState streamKey (read point) state).run H).2.length ≤ cost)
    (program : Tree Logical A Out rounds)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) (reserved : state.Reserved streamKey) :
    ((eagerState streamKey (expandQueries read program) state).run H).2.length ≤ cost*rounds := by
  induction program generalizing state with
  | done output => simp only [expandQueries,eagerState,Tree.run_done,List.length_nil,Nat.zero_le]
  | @query rounds point next ih =>
      rw [expandQueries,eagerState_comp,Tree.run_bind,List.length_append]
      have first := bounded point state H reserved
      have later := ih ((eagerState streamKey (read point) state).run H).1.1
        ((eagerState streamKey (read point) state).run H).1.2
        (eagerState_reserved streamKey (read point) state H reserved)
      have total := Nat.add_le_add first later
      simpa only [Nat.mul_succ,Nat.add_comm] using total

/-- Recording the raw trace changes only the output. It neither samples
extra coordinates nor hides any coordinate from the coupling's query log. -/
theorem eagerState_recordTrace_queries {Raw : Type} {fuel : ℕ}
    (encode : Raw → Point P K I) (program : Tree Raw D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    ((eagerState streamKey (mapQueries encode (recordTrace program)) state).run H).2 =
      ((eagerState streamKey (mapQueries encode program) state).run H).2 := by
  induction program generalizing state with
  | done output => rfl
  | query raw next ih =>
      cases encoded : encode raw with
      | inl point =>
          cases found : state.nodes point with
          | some digest =>
              simpa only [recordTrace,mapQueries,encoded,eagerState,found,Tree.run_weaken,
                mapQueries_map,eagerState_map,Tree.run_map] using ih digest state
          | none =>
              simp only [recordTrace,mapQueries,encoded,eagerState,found,Tree.run_query,
                mapQueries_map,eagerState_map,Tree.run_map]
              rw [ih]
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some row =>
              simpa only [recordTrace,mapQueries,encoded,eagerState,found,Tree.run_weaken,
                mapQueries_map,eagerState_map,Tree.run_map] using ih (row counter) state
          | none =>
              simp only [recordTrace,mapQueries,encoded,eagerState,found,Tree.run_query,
                mapQueries_map,eagerState_map,Tree.run_map]
              rw [ih]

/-- No answer is overwritten. This includes unobserved counter blocks of
a stream first allocated by an earlier node or an early PRF query. -/
theorem eagerState_extends {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    state.Extends ((eagerState streamKey program state).run H).1.2 := by
  induction program generalizing state with
  | done output => exact Cache.Extends.refl state
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simpa only [eagerState,found,Tree.run_weaken] using ih digest state
          | none =>
              simp only [eagerState,found,Tree.run_query]
              cases row : state.streams (streamKey point (H (.inl point)).1) with
              | some bytes =>
                  exact (state.node_extends point _ found).trans (ih _ _)
              | none =>
                  exact ((state.node_extends point _ found).trans
                    ((state.node point _).stream_extends _ _ row)).trans (ih _ _)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simpa only [eagerState,found,Tree.run_weaken] using ih (bytes counter) state
          | none =>
              simp only [eagerState,found,Tree.run_query]
              exact (state.stream_extends digest _ found).trans (ih _ _)

/-- The same raw oracle reproduces the source program and all node answers
used by the online history registry. Every sampled node was actually queried
by that raw program. No collision or speculative-query exclusion is needed. -/
theorem eagerState_source {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) (G : Point P K I → D)
    (agreement : ((eagerState streamKey program state).run H).1.2.Matches G) :
    (program.run G).1 = ((eagerState streamKey program state).run H).1.1 ∧
      ∀ point answer, ((.inl point,answer) : SamplePoint P K × Sample D I) ∈
        ((eagerState streamKey program state).run H).2 →
          G (.inl point) = answer.1 ∧ (.inl point : Point P K I) ∈ queried program G := by
  induction program generalizing state with
  | done output => exact ⟨rfl,fun _ _ h => nomatch h⟩
  | query point next ih =>
      have initial := Cache.Matches.of_extension (eagerState_extends streamKey (.query point next) state H) agreement
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest =>
              have answer := initial.1 point digest found
              have agrees : ((eagerState streamKey (next digest) state).run H).1.2.Matches G := by
                simpa only [eagerState,found,Tree.run_weaken] using agreement
              have later := ih digest state agrees
              constructor
              · simpa only [eagerState,found,Tree.run_weaken,Tree.run_query,answer] using later.1
              · intro other result member
                have present := later.2 other result (by
                  simpa only [eagerState,found,Tree.run_weaken] using member)
                refine ⟨present.1,?_⟩
                simpa only [queried,Tree.run_query,answer,List.map_cons] using
                  List.mem_cons_of_mem (.inl point : Point P K I) present.2
          | none =>
              let answer := H (.inl point)
              have rawAnswer : H (.inl point) = answer := rfl
              let after := match state.streams (streamKey point answer.1) with
                | some _ => state.node point answer.1
                | none => (state.node point answer.1).stream (streamKey point answer.1) answer.2
              have agrees : ((eagerState streamKey (next answer.1) after).run H).1.2.Matches G := by
                cases row : state.streams (streamKey point answer.1) <;>
                  simpa only [eagerState,found,Tree.run_query,after,rawAnswer,row] using agreement
              have afterMatches := Cache.Matches.of_extension (eagerState_extends streamKey (next answer.1) after H) agrees
              have current : G (.inl point) = answer.1 := afterMatches.1 point answer.1 (by
                dsimp [after]
                split <;> simp only [Cache.node,Cache.stream,Function.update_self])
              have later := ih answer.1 after agrees
              constructor
              · cases row : state.streams (streamKey point answer.1) <;>
                  simpa only [Tree.run_query,current,eagerState,found,after,rawAnswer,row] using later.1
              · intro other result member
                simp only [eagerState,found,Tree.run_query] at member
                change ((.inl other,result) : SamplePoint P K × Sample D I) ∈
                  (.inl point,answer)::((eagerState streamKey (next answer.1) after).run H).2 at member
                rcases List.mem_cons.mp member with same | member
                · obtain ⟨samePoint,sameAnswer⟩ := Prod.mk.inj same
                  cases Sum.inl.inj samePoint
                  cases sameAnswer
                  exact ⟨current,List.mem_cons_self⟩
                · have present := later.2 other result member
                  refine ⟨present.1,?_⟩
                  simpa only [queried,Tree.run_query,current,List.map_cons] using
                    List.mem_cons_of_mem (.inl point : Point P K I) present.2
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes =>
              have answer := initial.2 digest bytes found counter
              have agrees : ((eagerState streamKey (next (bytes counter)) state).run H).1.2.Matches G := by
                simpa only [eagerState,found,Tree.run_weaken] using agreement
              have later := ih (bytes counter) state agrees
              constructor
              · simpa only [eagerState,found,Tree.run_weaken,Tree.run_query,answer] using later.1
              · intro other result member
                have present := later.2 other result (by
                  simpa only [eagerState,found,Tree.run_weaken] using member)
                refine ⟨present.1,?_⟩
                simpa only [queried,Tree.run_query,answer,List.map_cons] using
                  List.mem_cons_of_mem (.inr (digest,counter) : Point P K I) present.2
          | none =>
              let answer := H (.inr digest)
              let after := state.stream digest answer.2
              have agrees : ((eagerState streamKey (next (answer.2 counter)) after).run H).1.2.Matches G := by
                simpa only [eagerState,found,Tree.run_query] using agreement
              have afterMatches := Cache.Matches.of_extension (eagerState_extends streamKey (next (answer.2 counter)) after H) agrees
              have current : G (.inr (digest,counter)) = answer.2 counter :=
                afterMatches.2 digest answer.2 (by simp only [after,Cache.stream,Function.update_self]) counter
              have later := ih (answer.2 counter) after agrees
              constructor
              · simpa only [Tree.run_query,current,eagerState,found] using later.1
              · intro other result member
                simp only [eagerState,found,Tree.run_query] at member
                change ((.inl other,result) : SamplePoint P K × Sample D I) ∈
                  (.inr digest,answer)::((eagerState streamKey (next (answer.2 counter)) after).run H).2 at member
                rcases List.mem_cons.mp member with same | member
                · cases (Prod.mk.inj same).1
                · have present := later.2 other result member
                  refine ⟨present.1,?_⟩
                  simpa only [queried,Tree.run_query,current,List.map_cons] using
                    List.mem_cons_of_mem (.inr (digest,counter) : Point P K I) present.2

/-- Retaining the raw trace proves cache coverage without unfolding the
query interpreter again. If an observed coordinate were missing, changing
that unconstrained coordinate would preserve the output but change an answer
in its recorded trace, contradicting source execution consistency. -/
theorem eagerState_recordTrace_covers [DecidableEq I] [Nontrivial D] {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) (state : Cache P K D I)
    (H : SamplePoint P K → Sample D I) :
    let result := ((eagerState streamKey (TranscriptV2.recordTrace program) state).run H).1
    ∀ point answer, (point,answer) ∈ result.1.2 → result.2.lookup point = some answer := by
  let result := ((eagerState streamKey (TranscriptV2.recordTrace program) state).run H).1
  change ∀ point answer, (point,answer) ∈ result.1.2 → result.2.lookup point = some answer
  intro point answer member
  have source (G : Point P K I → D) (agreement : result.2.Matches G) :
      program.run G = result.1 := by
    have actual := (eagerState_source streamKey (TranscriptV2.recordTrace program) state H G agreement).1
    simpa only [TranscriptV2.run_recordTrace] using actual
  cases found : result.2.lookup point with
  | some value =>
      let G := result.2.raw answer
      have actual := source G (Cache.matches_raw result.2 answer)
      have observed := Tree.trace_sound program G (point,answer) (by rw [actual]; exact member)
      have known := (Cache.matches_iff_lookup result.2 G).mp (Cache.matches_raw result.2 answer) point value found
      exact congrArg some (observed.trans known).symm
  | none =>
      obtain ⟨other,different⟩ := exists_ne answer
      let G := Function.update (result.2.raw answer) point other
      have agreement : result.2.Matches G := (Cache.matches_raw result.2 answer).update point found other
      have actual := source G agreement
      have observed := Tree.trace_sound program G (point,answer) (by rw [actual]; exact member)
      exact (different (by simpa only [G,Function.update_self] using observed.symm)).elim

end TranscriptV2.StrandCoupling
