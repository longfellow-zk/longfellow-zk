import Survival.ChronologicalAudit
import TranscriptV2.Queries

/-! State-dependent chronological audits retain the original query names.
Enrichment is used only to reuse the branch-mean theorem. Global backend
charges still live on the original finite oracle, so no total-table coupling
or independence claim about the enriched names is needed.
-/
noncomputable section
namespace Survival.History
open Finset Merkle.RandomOracle Bcs.FiniteProbability TranscriptV2 Bcs.TotalOracle
open scoped Classical

variable {P A Out S : Type}

def enrich (step : S → P → A → S) : {fuel : ℕ} → S → Tree P A Out fuel → Tree (S × P) A Out fuel
  | _, _, .done out => .done out
  | _, state, .query point next => .query (state,point) fun answer =>
      enrich step (step state point answer) (next answer)

def audit (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) : Tree P A (Bool × ℕ) fuel :=
  mapQueries Prod.snd (Hybrid.audit safe (fun point => marked point.2) (enrich step state tree))

theorem audit_query (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (point : P) (next : A → Tree P A Out fuel) :
    audit safe marked step state (.query point next) = .query point fun answer =>
      if safe (state,point) answer then
        (audit safe marked step (step state point answer) (next answer)).map fun result =>
          (result.1,result.2+if marked point then 1 else 0)
      else .done (true,if marked point then 1 else 0) := by
  simp only [audit, enrich, Hybrid.audit, mapQueries]
  congr 1
  funext answer
  by_cases hs : safe (state,point) answer
  · simp only [hs, if_true, mapQueries_map]
  · simp only [hs, if_false, mapQueries]

theorem audit_count (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A) :
    ((audit safe marked step state tree).run H).1.2 =
      (((audit safe marked step state tree).run H).2.filter fun qa => marked qa.1).length := by
  induction tree generalizing state with
  | done _ => rfl
  | query point next ih =>
      rw [audit_query, Merkle.RandomOracle.Tree.run_query]
      by_cases hs : safe (state,point) (H point)
      · simp only [hs, if_true, Merkle.RandomOracle.Tree.run_map]
        have counted := ih (H point) (step state point (H point))
        cases hm : marked point <;> simp [hm, counted, Nat.add_comm]
      · simp only [hs, if_false, Merkle.RandomOracle.Tree.run_done]
        cases hm : marked point <;> simp [hm]

theorem enrich_trace (step : S → P → A → S) {fuel : ℕ} (state : S)
    (tree : Tree P A Out fuel) (H : P → A) :
    ((enrich step state tree).run (fun point => H point.2)).2.map (fun qa => (qa.1.2,qa.2)) =
      (tree.run H).2 := by
  induction tree generalizing state with
  | done _ => rfl
  | query point next ih => simp only [enrich, Merkle.RandomOracle.Tree.run_query, List.map_cons, ih]

theorem audit_fresh [DecidableEq P] (safe : S × P → A → Prop) (marked : P → Bool)
    (step : S → P → A → S) {fuel : ℕ} (state : S) (tree : Tree P A Out fuel)
    {known : P → Prop} (fresh : FreshOracle.FreshFrom known tree) :
    FreshOracle.FreshFrom known (audit safe marked step state tree) := by
  induction tree generalizing state known with
  | done _ => simp only [audit, enrich, Hybrid.audit, mapQueries, FreshOracle.FreshFrom]
  | query point next ih =>
      refine ⟨fresh.1, fun answer => ?_⟩
      change FreshOracle.FreshFrom _ (mapQueries Prod.snd
        (if safe (state,point) answer then
          (Hybrid.audit safe (fun point => marked point.2)
            (enrich step (step state point answer) (next answer))).map _ else .done _))
      by_cases hs : safe (state,point) answer
      · simp only [hs, if_true, mapQueries_map]
        exact Hybrid.fresh_map _ _ (ih answer (step state point answer) (fresh.2 answer))
      · simp only [hs, if_false, mapQueries, FreshOracle.FreshFrom]

theorem audit_seen_subset [DecidableEq P] (safe : S × P → A → Prop) (marked : P → Bool)
    (step : S → P → A → S) {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A) :
    seen (audit safe marked step state tree) H ⊆ seen tree H := by
  induction tree generalizing state with
  | done _ => exact Finset.Subset.refl _
  | query point next ih =>
      rw [audit_query]
      intro p member
      by_cases hs : safe (state,point) (H point)
      · simp only [seen, queried, Merkle.RandomOracle.Tree.run_query, hs, if_true,
          Merkle.RandomOracle.Tree.run_map, List.map_cons, List.toFinset_cons] at member ⊢
        rcases Finset.mem_insert.mp member with same | tail
        · exact Finset.mem_insert.mpr (Or.inl same)
        · exact Finset.mem_insert.mpr (Or.inr (ih (H point) (step state point (H point)) tail))
      · simp only [seen, queried, Merkle.RandomOracle.Tree.run_query, hs, if_false,
          Merkle.RandomOracle.Tree.run_done, List.map_cons, List.map_nil, List.toFinset_cons,
          List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at member
        subst p
        simp [seen, queried_query]

private theorem pure_audit_trace [DecidableEq P] (safe : P → A → Prop) (marked : P → Bool)
    {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((Hybrid.audit safe marked tree).run H).1.1 = false) :
    ((Hybrid.audit safe marked tree).run H).2 = (tree.run H).2 := by
  induction tree with
  | done _ => rfl
  | query point next ih =>
      by_cases hs : safe point (H point)
      · simp only [Hybrid.audit, Merkle.RandomOracle.Tree.run_query, hs, if_true,
          Merkle.RandomOracle.Tree.run_map] at survived ⊢
        rw [ih (H point) survived]
      · simp only [Hybrid.audit, Merkle.RandomOracle.Tree.run_query, hs, if_false,
          Merkle.RandomOracle.Tree.run_done] at survived
        cases survived

theorem audit_trace [DecidableEq P] (safe : S × P → A → Prop) (marked : P → Bool)
    (step : S → P → A → S) {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((audit safe marked step state tree).run H).1.1 = false) :
    ((audit safe marked step state tree).run H).2 = (tree.run H).2 := by
  simp only [audit, run_mapQueries] at survived ⊢
  rw [pure_audit_trace safe (fun point => marked point.2) (enrich step state tree)
    (H ∘ Prod.snd) survived]
  exact enrich_trace step state tree H

private def firstInTrace [DecidableEq P] (parent child : P) : List (P × A) → FirstOfTwo
  | [] => .neither
  | qa::rest => if qa.1 = parent then .left else if qa.1 = child then .right else firstInTrace parent child rest

private theorem firstOfTwo_trace [DecidableEq P] {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (parent child : P) :
    firstOfTwo tree H parent child = firstInTrace parent child (tree.run H).2 := by
  induction tree with
  | done _ => rfl
  | query point next ih => simp only [firstOfTwo, Merkle.RandomOracle.Tree.run_query, firstInTrace, ih]

theorem order_of_trace [DecidableEq P] {X Y : Type} {fuel extra : ℕ}
    (first : Tree P A X fuel) (second : Tree P A Y extra) (H : P → A)
    (same : (first.run H).2 = (second.run H).2) (parent child : P) :
    firstOfTwo first H parent child = firstOfTwo second H parent child := by
  rw [firstOfTwo_trace, firstOfTwo_trace, same]

theorem order_preserved [DecidableEq P] (safe : S × P → A → Prop) (marked : P → Bool)
    (step : S → P → A → S) {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((audit safe marked step state tree).run H).1.1 = false) (parent child : P) :
    firstOfTwo (audit safe marked step state tree) H parent child = firstOfTwo tree H parent child :=
  order_of_trace _ _ H (audit_trace safe marked step state tree H survived) parent child

theorem cut_preserved [DecidableEq P] {Key : Type} [DecidableEq Key]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((audit safe marked step state tree).run H).1.1 = false)
    (label : P → Key) (key : Key) :
    beforeLabel label key (audit safe marked step state tree) H = beforeLabel label key tree H := by
  rw [beforeLabel_eq_takeWhile, beforeLabel_eq_takeWhile, audit_trace safe marked step state tree H survived]

theorem safe_at_prefix (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((audit safe marked step state tree).run H).1.1 = false)
    (past rest : List (P × A)) (point : P) (answer : A)
    (trace : (tree.run H).2 = past ++ (point,answer)::rest) :
    safe (past.foldl (fun s qa => step s qa.1 qa.2) state, point) answer := by
  induction tree generalizing state past with
  | done _ => simp only [Merkle.RandomOracle.Tree.run_done] at trace; simp at trace
  | query current next ih =>
      rw [audit_query, Merkle.RandomOracle.Tree.run_query] at survived
      by_cases hs : safe (state,current) (H current)
      · simp only [hs, if_true, Merkle.RandomOracle.Tree.run_map] at survived
        cases past with
        | nil =>
            have same := List.cons.inj trace |>.1
            have points := congrArg Prod.fst same
            have answers := congrArg Prod.snd same
            change current = point at points
            change H current = answer at answers
            simp only [List.foldl_nil]
            rw [← points, ← answers]
            exact hs
        | cons qa past =>
            have parts := List.cons.inj trace
            have points := congrArg Prod.fst parts.1
            have answers := congrArg Prod.snd parts.1
            change current = qa.1 at points
            change H current = qa.2 at answers
            have tail := ih (H current) (step state current (H current)) survived past parts.2
            simp only [List.foldl_cons]
            rw [← points, ← answers]
            exact tail
      · simp only [hs, if_false, Merkle.RandomOracle.Tree.run_done] at survived
        cases survived

end Survival.History
