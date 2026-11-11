import LfzkV2.Current.StrandPath

/-! Recognition uses only the recorded SHA answers. A logical name already
recovered by the online decoder must match the verifier's canonical history,
unless two queried node inputs collide. The scope predicate below will be the
finite set of actual search and replay inputs, never all possible SHA inputs. -/
noncomputable section
namespace LfzkV2.Current.StrandRecognition
open Finset Merkle.RandomOracle TranscriptV2
open TranscriptV2.Strand TranscriptV2.StrandCoupling
open scoped Classical

variable {P T : Type}
variable (schema : History.Codec T) (bytes : P → Framing.Bytes)

local notation "Name" => StrandSearch.Name P T
local notation "Answer" => Sample Digest Word
local notation "name" => StrandSearch.name schema bytes
local notation "advance" => StrandSearch.advance bytes

private def table (trace : List (Name × Answer)) : List Entry :=
  trace.foldl (fun state qa => advance state (StrandSearch.erase qa.1) qa.2) []

private theorem table_scope (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace)
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ trace → scope (bytes raw))
    (entry : Entry) (member : entry ∈ table bytes trace) :
    ∀ raw ∈ entry.history.ancestors, scope raw := by
  have closed := StrandPath.closed_fold bytes [] trace closed_nil
  have supported := StrandPath.trace_supported schema bytes trace named
  intro raw ancestor
  obtain ⟨known,registered,encoded⟩ := closed entry member raw ancestor
  obtain ⟨point,answer,queried,_,input⟩ := supported known registered
  rw [encoded,input]
  exact inside point _ answer queried

/-- Every ordinary label at an actual query agrees with the verifier's
history of that input, outside collisions on their queried ancestors. -/
theorem ordinary_matches (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ trace →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ trace → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (raw : P) (value expected : T) (answer : Answer)
    (member : ((.inl (raw,some value),answer) : Name × Answer) ∈ trace)
    (actual : (schema.encode expected).Consistent G)
    (encoded : bytes raw = (schema.encode expected).input.encode)
    (ancestors : ∀ point ∈ (schema.encode expected).ancestors, scope point) : value = expected := by
  obtain ⟨first,rest,splitTrace⟩ := List.append_of_mem member
  have namedSplit := splitTrace ▸ named
  have earlier qa (member : qa ∈ first) : qa ∈ trace := by
    rw [splitTrace]
    exact List.mem_append_left _ member
  have insideFirst raw logical answer member := inside raw logical answer (earlier _ member)
  have parsed : StrandSearch.decode schema bytes (table bytes first) raw = some value :=
    (Prod.mk.inj (Sum.inl.inj namedSplit.name_after)).2
  have sound := StrandPath.consistent_fold bytes G [] first (fun _ h => nomatch h)
    (fun raw logical answer member => answers raw logical answer (earlier _ member))
  apply StrandPath.decoded_matches schema bytes G (table bytes first) sound raw value expected parsed actual encoded
  obtain ⟨history,unfolded,decoded⟩ := Option.bind_eq_some_iff.mp parsed
  have canonical := schema.canonical history value decoded
  intro a ancestorA b ancestorB same
  apply collisionFree a _ b (ancestors b ancestorB) same
  rw [canonical] at ancestorA
  rcases unfoldNode_past (table bytes first) (StrandPath.closed_fold bytes [] first closed_nil)
      (bytes raw) history unfolded a ancestorA with current | registered
  · rw [current]
    exact inside raw _ answer member
  · obtain ⟨entry,present,input⟩ := registered
    rw [input]
    exact table_scope schema bytes first namedSplit.append.1 scope insideFirst entry present
      entry.history.input.encode entry.history.mem_ancestors

/-- A previously recognized parent can be used without an arbitrary
tie-breaking assumption. All equal-digest entries have the same history
outside the stated collision event, so the decoder's first match is correct. -/
theorem resolve_parent (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ trace →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ trace → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (raw : P) (parent : T) (answer : Answer)
    (member : ((.inl (raw,some parent),answer) : Name × Answer) ∈ trace)
    (actual : (schema.encode parent).Consistent G)
    (encoded : bytes raw = (schema.encode parent).input.encode)
    (ancestors : ∀ point ∈ (schema.encode parent).ancestors, scope point) :
    resolve (table bytes trace) (G (bytes raw)) = some (schema.encode parent) := by
  have known := StrandPath.ordinary_recorded schema bytes [] trace named raw parent answer member
  have sound := StrandPath.consistent_fold bytes G [] trace (fun _ h => nomatch h) answers
  apply resolve_complete (table bytes trace) (G (bytes raw)) (schema.encode parent)
  · exact ⟨⟨schema.encode parent,answer.1⟩,known,answers raw _ answer member⟩
  · intro entry present same
    have consistent := sound entry present
    have entryScope := table_scope schema bytes trace named scope inside entry present
    have input : entry.history.input.encode = (schema.encode parent).input.encode := by
      apply collisionFree _ (entryScope _ entry.history.mem_ancestors) _ (ancestors _ (schema.encode parent).mem_ancestors)
      exact consistent.2.symm.trans (same.trans (congrArg G encoded))
    exact History.erasure_injective G entry.history (schema.encode parent) consistent.1 actual
      (fun a ha b hb equal => collisionFree a (entryScope a ha) b (ancestors b hb) equal) input

private theorem root_recognized (trace : List (Name × Answer))
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] trace)
    (raw : P) (logical : Option T) (expected : T) (answer : Answer)
    (member : ((.inl (raw,logical),answer) : Name × Answer) ∈ trace)
    (encoded : bytes raw = (schema.encode expected).input.encode)
    (root : ∃ message, schema.encode expected = .root message) : logical = some expected := by
  obtain ⟨first,rest,splitTrace⟩ := List.append_of_mem member
  have namedSplit := splitTrace ▸ named
  have selected : StrandSearch.decode schema bytes (table bytes first) raw = logical :=
    (Prod.mk.inj (Sum.inl.inj namedSplit.name_after)).2
  rw [← selected]
  obtain ⟨message,shape⟩ := root
  have input : bytes raw = (Strand.Input.root message).encode := by rw [encoded,shape]; rfl
  have inverse := schema.inverse expected
  rw [shape] at inverse
  simp only [StrandSearch.decode,unfoldNode,input,Strand.Input.decode_encode (.root message) trivial,
    Option.bind_eq_bind,Option.bind_some,unfoldInput,inverse]

variable [DecidableEq P]

/-- If a child was left auxiliary, its named parent digest was speculative.
Outside the charged guess event, the parent's already recognized query must
precede it; the registry then decodes the child as the verifier's actual node. -/
theorem child_recognized {Out : Type} {fuel : ℕ} (tree : Tree Name Answer Out fuel)
    (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) tree H)
    (parentRaw raw : P) (parent expected : T) (parentAnswer answer : Answer) (logical : Option T)
    (parentQuery : ((.inl (parentRaw,some parent),parentAnswer) : Name × Answer) ∈ (tree.run H).2)
    (member : ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2)
    (parentEncoded : bytes parentRaw = (schema.encode parent).input.encode)
    (encoded : bytes raw = (schema.encode expected).input.encode)
    (actual : (schema.encode expected).Consistent G)
    (ancestors : ∀ point ∈ (schema.encode expected).ancestors, scope point)
    (previous : ∃ digest message, schema.encode expected = .child (schema.encode parent) digest message)
    (bounded : (schema.encode expected).depth < 2^64) :
    logical = some expected := by
  cases logical with
  | some value =>
      exact congrArg some (ordinary_matches schema bytes (tree.run H).2 named G answers scope inside
        collisionFree raw value expected answer member actual encoded ancestors)
  | none =>
      obtain ⟨digest,message,shape⟩ := previous
      have consistent : (schema.encode parent).Consistent G ∧ digest = G (schema.encode parent).input.encode := by
        rw [shape] at actual
        exact actual
      have parentAncestors point (ancestor : point ∈ (schema.encode parent).ancestors) : scope point := by
        apply ancestors point
        rw [shape]
        exact List.mem_cons_of_mem _ ancestor
      have input : bytes raw = (Strand.Input.node (History.child (schema.encode parent) digest message).id [digest] message).encode := by rw [encoded,shape]; rfl
      have hParent : (.inl (parentRaw,some parent) : Name) ∈ seen tree H :=
        List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) parentQuery)
      have hChild : (.inl (raw,none) : Name) ∈ seen tree H :=
        List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) member)
      have parentAnswerEq : (H (.inl (parentRaw,some parent))).1 = G (bytes parentRaw) := by
        rw [← Tree.trace_sound tree H _ parentQuery]
        exact answers parentRaw _ parentAnswer parentQuery
      have claimed : (H (.inl (parentRaw,some parent))).1 ∈
          StrandSearch.claims bytes (.inl (raw,none) : Name) := by
        rw [parentAnswerEq,parentEncoded,← consistent.2]
        simp only [StrandSearch.claims,input,Strand.Input.decode_encode (.node (History.child (schema.encode parent) digest message).id [digest] message)
          ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩,mem_singleton]
      have preceding := DigestProjection.parent_before_child (StrandSearch.claims bytes)
        tree H noGuess _ _ hParent hChild claimed
      obtain ⟨first,rest,current,splitTrace,past⟩ := trace_split_before tree H _ hChild
      have namedSplit := splitTrace ▸ named
      rw [← past] at preceding
      obtain ⟨⟨prior,priorAnswer⟩,inFirst,same⟩ := List.mem_map.mp preceding
      change prior = .inl (parentRaw,some parent) at same
      subst prior
      have earlier qa (member : qa ∈ first) : qa ∈ (tree.run H).2 := by
        rw [splitTrace]
        exact List.mem_append_left _ member
      have resolved := resolve_parent schema bytes first namedSplit.append.1 G
        (fun raw logical answer member => answers raw logical answer (earlier _ member)) scope
        (fun raw logical answer member => inside raw logical answer (earlier _ member)) collisionFree
        parentRaw parent priorAnswer inFirst consistent.1 parentEncoded parentAncestors
      rw [parentEncoded,← consistent.2] at resolved
      have missing : StrandSearch.decode schema bytes (table bytes first) raw = none :=
        (Prod.mk.inj (Sum.inl.inj namedSplit.name_after)).2
      have depthBound : (schema.encode parent).depth+1 < 2^64 := by
        simpa only [shape,History.depth] using bounded
      have inverse := schema.inverse expected
      rw [shape] at inverse
      simp only [StrandSearch.decode,unfoldNode,input,Strand.Input.decode_encode (.node (History.child (schema.encode parent) digest message).id [digest] message)
        ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩,Option.bind_eq_bind,Option.bind_some,
        unfoldInput,resolved,Option.filter_some,depthBound,true_and,decide_true,ite_true,Option.map_some,inverse] at missing
      cases missing

/-- Raw visibility of the verifier path gives recognition of every query
on it, outside collisions and the charged speculative-target event. Visibility
will come from running the verifier; it does not assert logical decoding or
chronological order of the adversary's queries. -/
theorem path_recognized {Out : Type} {fuel rounds : ℕ} (tree : Tree Name Answer Out fuel)
    (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) tree H)
    (path : ℕ → T) (locate : T → P)
    (located : ∀ value, bytes (locate value) = (schema.encode value).input.encode)
    (actual : ∀ i ≤ rounds, (schema.encode (path i)).Consistent G)
    (bounded : ∀ i ≤ rounds, (schema.encode (path i)).depth < 2^64)
    (root : ∃ message, schema.encode (path 0) = .root message)
    (previous : ∀ i < rounds, ∃ digest message,
      schema.encode (path (i+1)) = .child (schema.encode (path i)) digest message)
    (visible : ∀ i ≤ rounds, ∃ logical answer,
      ((.inl (locate (path i),logical),answer) : Name × Answer) ∈ (tree.run H).2) :
    ∀ i ≤ rounds, ∀ logical answer,
      ((.inl (locate (path i),logical),answer) : Name × Answer) ∈ (tree.run H).2 →
        logical = some (path i) := by
  have nodeScope i (within : i ≤ rounds) : scope (schema.encode (path i)).input.encode := by
    obtain ⟨logical,answer,queried⟩ := visible i within
    rw [← located]
    exact inside _ logical answer queried
  have ancestorScope i (within : i ≤ rounds) :
      ∀ point ∈ (schema.encode (path i)).ancestors, scope point := by
    induction i with
    | zero =>
        obtain ⟨message,shape⟩ := root
        intro point member
        rw [shape] at member
        simp only [History.ancestors,List.mem_cons,List.not_mem_nil,or_false] at member
        rw [member,← shape]
        exact nodeScope 0 within
    | succ i ih =>
        obtain ⟨digest,message,shape⟩ := previous i (by omega)
        intro point member
        rw [shape] at member
        rcases List.mem_cons.mp member with current | ancestor
        · rw [current,← shape]
          exact nodeScope (i+1) within
        · exact ih (by omega) point ancestor
  intro i within
  induction i with
  | zero =>
      intro logical answer member
      exact root_recognized schema bytes _ named _ logical (path 0) answer member (located _) root
  | succ i ih =>
      intro logical answer member
      obtain ⟨prior,priorAnswer,queried⟩ := visible i (by omega)
      have recognized := ih (by omega) prior priorAnswer queried
      rw [recognized] at queried
      exact child_recognized schema bytes tree H named G answers scope inside collisionFree noGuess
        _ _ (path i) (path (i+1)) priorAnswer answer logical queried member (located _) (located _)
        (actual (i+1) within) (ancestorScope (i+1) within) (previous i (by omega)) (bounded (i+1) within)

/-- Raw visibility in the original search suffices for chronological typed
path recovery. This form has no verifier-replay or final-seal hypotheses;
clients establish original visibility with their own explicit event cover. -/
theorem original_path_or_charge {Out : Type} {fuel rounds : ℕ}
    (tree : Tree Name Answer Out fuel) (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ (tree.run H).2 → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (injective : Function.Injective bytes) (path : ℕ → T) (locate : T → P)
    (located : ∀ value, bytes (locate value) = (schema.encode value).input.encode)
    (actual : ∀ i ≤ rounds, (schema.encode (path i)).Consistent G)
    (bounded : ∀ i ≤ rounds, (schema.encode (path i)).depth < 2^64)
    (root : ∃ message, schema.encode (path 0) = .root message)
    (previous : ∀ i < rounds, ∃ digest message,
      schema.encode (path (i+1)) = .child (schema.encode (path i)) digest message)
    (visible : ∀ i ≤ rounds, ∃ logical answer,
      ((.inl (locate (path i),logical),answer) : Name × Answer) ∈ (tree.run H).2) :
    Composition.PathQueries (rounds := rounds) tree H (fun i => .inl (locate (path i),some (path i))) ∨
      1 ≤ DigestProjection.charge (StrandSearch.claims bytes) tree H := by
  by_cases guessed : DigestProjection.Guess (StrandSearch.claims bytes) tree H
  · exact Or.inr (DigestProjection.guess_charged _ _ _ guessed)
  · have recognized := path_recognized schema bytes tree H named G answers scope inside collisionFree
      guessed path locate located actual bounded root previous visible
    obtain ⟨logical,answer,present⟩ := visible rounds le_rfl
    rw [recognized _ le_rfl _ _ present] at present
    exact Or.inl (StrandPath.path_queries schema bytes tree H named injective locate located path previous
      (List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) present)))

private theorem stream_source_parent {Out Result : Type} {fuel extra : ℕ}
    (tree : Tree Name Answer Out fuel) (replay : Out → Tree Name Answer Result extra)
    (H : Name → Answer) (raw : P) (logical : Option T) (answer : Answer)
    (visible : ((.inl (raw,logical),answer) : Name × Answer) ∈ ((tree.bind replay).run H).2)
    (source : ∃ point result, (point,result) ∈ (tree.run H).2 ∧
      (streamKey (StrandSearch.key bytes) (StrandSearch.erase point) result).2 = answer.1)
    (unique : ∀ point decoded result, ((.inl (point,decoded),result) : Name × Answer) ∈
      ((tree.bind replay).run H).2 → result.1 = answer.1 → point = raw)
    (noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) (tree.bind replay) H) :
    ∃ decoded result, ((.inl (raw,decoded),result) : Name × Answer) ∈ (tree.run H).2 := by
  obtain ⟨point,result,queried,key⟩ := source
  cases point with
  | inl point =>
      rcases point with ⟨point,decoded⟩
      have included : ((.inl (point,decoded),result) : Name × Answer) ∈ ((tree.bind replay).run H).2 := by
        rw [Tree.run_bind]
        exact List.mem_append_left _ queried
      have same := unique point decoded result included key
      subst point
      exact ⟨decoded,result,queried⟩
  | inr digest =>
      have parent : (.inl (raw,logical) : Name) ∈ seen (tree.bind replay) H :=
        List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) visible)
      have child : (.inr digest : Name) ∈ seen tree H :=
        List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) queried)
      have claimed : (H (.inl (raw,logical))).1 ∈ StrandSearch.claims bytes (.inr digest : Name) := by
        rw [← Tree.trace_sound (tree.bind replay) H _ visible]
        exact mem_singleton.mpr key.symm
      have previous := DigestProjection.parent_in_search (StrandSearch.claims bytes) tree replay H noGuess
        (.inl (raw,logical)) (.inr digest) parent child claimed
      obtain ⟨⟨point,result⟩,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp previous)
      change point = .inl (raw,logical) at same
      subst point
      exact ⟨logical,result,member⟩

/-- Recovery spends only the original search budget. A final PRF stream
already obtained by the search comes either from its final node or from an
early PRF query. The latter forces the node back into the search, except for
the charged guess event. Replay itself supplies no algebraic-query allowance.
The final-seal argument must establish that this stream was obtained. -/
theorem path_or_charge {Out Result : Type} {fuel extra rounds : ℕ}
    (tree : Tree Name Answer Out fuel) (replay : Out → Tree Name Answer Result extra)
    (H : Name → Answer)
    (named : FreshOracle.NamedTrace name advance StrandSearch.erase [] ((tree.bind replay).run H).2)
    (G : Strand.Oracle)
    (answers : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ ((tree.bind replay).run H).2 →
      answer.1 = G (bytes raw))
    (scope : Framing.Bytes → Prop)
    (inside : ∀ raw logical answer, ((.inl (raw,logical),answer) : Name × Answer) ∈ ((tree.bind replay).run H).2 → scope (bytes raw))
    (collisionFree : ∀ a, scope a → ∀ b, scope b → G a = G b → a = b)
    (noReplayHit : ¬∃ p, DigestProjection.Replay.bad (StrandSearch.claims bytes) tree replay p H (H p))
    (path : ℕ → T) (locate : T → P) (injective : Function.Injective bytes)
    (located : ∀ value, bytes (locate value) = (schema.encode value).input.encode)
    (actual : ∀ i ≤ rounds, (schema.encode (path i)).Consistent G)
    (bounded : ∀ i ≤ rounds, (schema.encode (path i)).depth < 2^64)
    (root : ∃ message, schema.encode (path 0) = .root message)
    (previous : ∀ i < rounds, ∃ digest message,
      schema.encode (path (i+1)) = .child (schema.encode (path i)) digest message)
    (visible : ∀ i ≤ rounds, ∃ logical answer,
      ((.inl (locate (path i),logical),answer) : Name × Answer) ∈ ((tree.bind replay).run H).2)
    (finalStream : ∃ point answer, (point,answer) ∈ (tree.run H).2 ∧
      (streamKey (StrandSearch.key bytes) (StrandSearch.erase point) answer).2 = G (bytes (locate (path rounds)))) :
    Composition.PathQueries (rounds := rounds) tree H
        (fun i => .inl (locate (path i),some (path i))) ∨
      1 ≤ DigestProjection.charge (StrandSearch.claims bytes) tree H := by
  by_cases guessed : DigestProjection.Guess (StrandSearch.claims bytes) tree H
  · exact Or.inr (DigestProjection.guess_charged (StrandSearch.claims bytes) tree H guessed)
  · have noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) (tree.bind replay) H := by
      intro hit
      exact (DigestProjection.Replay.guess_split (StrandSearch.claims bytes) tree replay H hit).elim
        guessed noReplayHit
    have recognized := path_recognized schema bytes (tree.bind replay) H named G answers scope inside
      collisionFree noGuess path locate located actual bounded root previous visible
    obtain ⟨lastLogical,lastAnswer,lastQuery⟩ := visible rounds le_rfl
    have source : ∃ point answer, (point,answer) ∈ (tree.run H).2 ∧
        (streamKey (StrandSearch.key bytes) (StrandSearch.erase point) answer).2 = lastAnswer.1 := by
      obtain ⟨point,answer,member,key⟩ := finalStream
      exact ⟨point,answer,member,key.trans (answers _ _ _ lastQuery).symm⟩
    have unique point decoded result (member : ((.inl (point,decoded),result) : Name × Answer) ∈
        ((tree.bind replay).run H).2) (same : result.1 = lastAnswer.1) : point = locate (path rounds) := by
      apply injective
      exact collisionFree _ (inside _ _ _ member) _ (inside _ _ _ lastQuery)
        ((answers _ _ _ member).symm.trans (same.trans (answers _ _ _ lastQuery)))
    obtain ⟨logical,answer,queried⟩ := stream_source_parent bytes tree replay H _ _ _ lastQuery source unique noGuess
    have terminalFull : ((.inl (locate (path rounds),logical),answer) : Name × Answer) ∈
        ((tree.bind replay).run H).2 := by
      rw [Tree.run_bind]
      exact List.mem_append_left _ queried
    rw [recognized rounds le_rfl logical answer terminalFull] at queried
    have namedSearch : FreshOracle.NamedTrace name advance StrandSearch.erase [] (tree.run H).2 := by
      rw [Tree.run_bind] at named
      exact named.append.1
    exact Or.inl (StrandPath.path_queries schema bytes tree H namedSearch injective locate located path previous
      (List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) queried)))

end LfzkV2.Current.StrandRecognition
