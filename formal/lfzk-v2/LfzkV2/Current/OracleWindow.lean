import Merkle.TreeCompose

/-! A bounded oracle program uses a finite marginal even when raw inputs
are arbitrary byte strings.  Its answer type is finite, so there are only
finitely many branches and finitely many possible query inputs.

The transport preserves both the output and the complete query/answer trace.
No independence, freshness or collision premise is needed. -/
noncomputable section
namespace LfzkV2.Current.OracleWindow

open Merkle.RandomOracle Finset
open scoped Classical

variable {Query Answer Output : Type} [Fintype Answer] [DecidableEq Query]

/-- All query inputs on every answer branch, not merely the inputs on one
particular execution. The raw input type itself need not be finite. -/
def queries : {fuel : ℕ} → Tree Query Answer Output fuel → Finset Query
  | _, .done _ => ∅
  | _, .query query next => insert query (univ.biUnion fun answer => queries (next answer))

theorem trace_mem_queries {fuel : ℕ} (body : Tree Query Answer Output fuel)
    (H : Query → Answer) (qa : Query × Answer) (member : qa ∈ (body.run H).2) :
    qa.1 ∈ queries body := by
  induction body with
  | done out => simp only [Tree.run_done,List.not_mem_nil] at member
  | query query next ih =>
      simp only [Tree.run_query,List.mem_cons] at member
      rcases member with rfl | tail
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_biUnion.mpr ⟨H query,mem_univ _,ih (H query) tail⟩)

/-- Restrict the program, not just the oracle, to a finite query window. -/
def restrict (window : Finset Query) : {fuel : ℕ} →
    (body : Tree Query Answer Output fuel) → queries body ⊆ window →
      Tree {query // query ∈ window} Answer Output fuel
  | _, .done out, _ => .done out
  | _, .query query next, contains =>
      .query ⟨query,contains (mem_insert_self _ _)⟩ fun answer =>
        restrict window (next answer) fun _point member =>
          contains (mem_insert_of_mem (mem_biUnion.mpr ⟨answer,mem_univ _,member⟩))

/-- Forgetting the finite-window subtype recovers the exact full trace.
This permits every later observer, including one inspecting repeated queries,
to be transported without replacing its view by an output-only model. -/
theorem restrict_run (window : Finset Query) {fuel : ℕ}
    (body : Tree Query Answer Output fuel) (contains : queries body ⊆ window)
    (H : Query → Answer) :
    (((restrict window body contains).run (fun query => H query.val)).1,
      ((restrict window body contains).run (fun query => H query.val)).2.map
        (fun qa => (qa.1.val,qa.2))) = body.run H := by
  induction body with
  | done out => rfl
  | query query next ih =>
      simp only [restrict,Tree.run_query,List.map_cons]
      have tail := ih (H query) (fun _point member =>
        contains (mem_insert_of_mem (mem_biUnion.mpr ⟨H query,mem_univ _,member⟩)))
      have output := congrArg Prod.fst tail
      have trace := congrArg Prod.snd tail
      exact Prod.ext output (congrArg (List.cons (query,H query)) trace)

/-- Extend a finite oracle arbitrarily away from its query window. -/
def extend (window : Finset Query) (H : {query // query ∈ window} → Answer)
    (outside : Query → Answer) (query : Query) : Answer :=
  if member : query ∈ window then H ⟨query,member⟩ else outside query

omit [Fintype Answer] in
theorem extend_mem (window : Finset Query) (H : {query // query ∈ window} → Answer)
    (outside : Query → Answer) (query : Query) (member : query ∈ window) :
    extend window H outside query = H ⟨query,member⟩ := dif_pos member

/-- The finite program can be executed directly against its uniform finite
oracle; extending that oracle to arbitrary raw strings recovers exactly the
same output and trace after forgetting subtype proofs. -/
theorem restrict_extend_run (window : Finset Query) {fuel : ℕ}
    (body : Tree Query Answer Output fuel) (contains : queries body ⊆ window)
    (H : {query // query ∈ window} → Answer) (outside : Query → Answer) :
    (((restrict window body contains).run H).1,
      ((restrict window body contains).run H).2.map (fun qa => (qa.1.val,qa.2))) =
        body.run (extend window H outside) := by
  have values : (fun query : {query // query ∈ window} =>
      extend window H outside query.val) = H := by
    funext query
    simp only [extend,query.property,↓reduceDIte]
  simpa only [values] using restrict_run window body contains (extend window H outside)

theorem queries_bind_left {Next : Type} {fuel nextFuel : ℕ}
    (body : Tree Query Answer Output fuel) (next : Output → Tree Query Answer Next nextFuel) :
    queries body ⊆ queries (body.bind next) := by
  induction body with
  | done out => exact empty_subset _
  | query query continuation ih =>
      intro point member
      simp only [queries,mem_insert] at member
      simp only [Tree.bind,queries,mem_insert]
      rcases member with same | member
      · exact Or.inl same
      · obtain ⟨answer,_,member⟩ := mem_biUnion.mp member
        exact Or.inr (mem_biUnion.mpr ⟨answer,mem_univ _,ih answer member⟩)

end LfzkV2.Current.OracleWindow
