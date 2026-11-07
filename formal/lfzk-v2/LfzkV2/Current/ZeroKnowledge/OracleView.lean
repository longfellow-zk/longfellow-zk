import Merkle.TreeCompose

/-! An oracle observer sees its own complete query/answer trace, including
repeats. Recording that view is a syntactic transformation of the same query
tree: it performs no extra query and exposes no unqueried oracle coordinate.
The background table used in simulator couplings is not part of this view. -/
namespace LfzkV2.Current.ZeroKnowledge.OracleView
open Merkle.RandomOracle

variable {Query Answer Value : Type}

def record : {fuel : ℕ} → Tree Query Answer Value fuel →
    Tree Query Answer (Value × List (Query × Answer)) fuel
  | _,.done value => .done (value,[])
  | _,.query query next => .query query fun answer =>
      (record (next answer)).map fun rest => (rest.1,(query,answer)::rest.2)

/-- The returned trace is exactly the observer's own ordinary execution
trace. Recording cannot inspect or serialize the full oracle table. -/
theorem record_run {fuel : ℕ} (tree : Tree Query Answer Value fuel) (H : Query → Answer) :
    (record tree).run H = (tree.run H,(tree.run H).2) := by
  induction tree with
  | done value => rfl
  | @query fuel query next ih =>
      simp only [record,Tree.run_query,Tree.run_map,ih]

@[simp] theorem record_output {fuel : ℕ} (tree : Tree Query Answer Value fuel) (H : Query → Answer) :
    ((record tree).run H).1 = tree.run H := congrArg Prod.fst (record_run tree H)

@[simp] theorem record_trace {fuel : ℕ} (tree : Tree Query Answer Value fuel) (H : Query → Answer) :
    ((record tree).run H).2 = (tree.run H).2 := congrArg Prod.snd (record_run tree H)

end LfzkV2.Current.ZeroKnowledge.OracleView
