import Survival.History

/-! Separate syntactic fuel from the number of distinct original queries.
Memoization may retain a huge fuel index while making only Q fresh draws.
Rebudgeting preserves the complete trace, monitor, and stopped audit.
-/
noncomputable section
namespace Survival.QueryBudget
open Merkle.RandomOracle Bcs.TotalOracle
open scoped Classical

variable {P A Out : Type}

def AtMost : {fuel : ℕ} → ℕ → Tree P A Out fuel → Prop
  | _, _, .done _ => True
  | _, 0, .query _ _ => False
  | _, budget+1, .query _ next => ∀ answer, AtMost budget (next answer)

def cap : {fuel : ℕ} → (budget : ℕ) → (tree : Tree P A Out fuel) → AtMost budget tree → Tree P A Out budget
  | _, _, .done out, _ => .done out
  | _, 0, .query _ _, impossible => False.elim impossible
  | _, budget+1, .query point next, bounded =>
      .query point fun answer => cap budget (next answer) (bounded answer)

theorem cap_run {fuel budget : ℕ} (tree : Tree P A Out fuel) (bounded : AtMost budget tree)
    (H : P → A) : (cap budget tree bounded).run H = tree.run H := by
  induction tree generalizing budget with
  | done _ => cases budget <;> rfl
  | query point next ih =>
      cases budget with
      | zero => exact False.elim bounded
      | succ budget => simp only [cap, Merkle.RandomOracle.Tree.run_query, ih]

theorem cap_fresh {fuel budget : ℕ} (tree : Tree P A Out fuel) (bounded : AtMost budget tree)
    {known : P → Prop} (fresh : TranscriptV2.FreshOracle.FreshFrom known tree) :
    TranscriptV2.FreshOracle.FreshFrom known (cap budget tree bounded) := by
  induction tree generalizing budget known with
  | done _ => cases budget <;> trivial
  | query point next ih =>
      cases budget with
      | zero => exact False.elim bounded
      | succ budget => exact ⟨fresh.1, fun a => ih a (bounded a) (fresh.2 a)⟩

theorem cap_audit_run (safe : P → A → Prop) (marked : P → Bool)
    {fuel budget : ℕ} (tree : Tree P A Out fuel) (bounded : AtMost budget tree) (H : P → A) :
    (Hybrid.audit safe marked (cap budget tree bounded)).run H = (Hybrid.audit safe marked tree).run H := by
  induction tree generalizing budget with
  | done _ => cases budget <;> rfl
  | query point next ih =>
      cases budget with
      | zero => exact False.elim bounded
      | succ budget =>
          simp only [cap, Hybrid.audit, Merkle.RandomOracle.Tree.run_query]
          by_cases hs : safe point (H point)
          · simp only [hs, if_true, Merkle.RandomOracle.Tree.run_map, ih]
          · simp only [hs, if_false, Merkle.RandomOracle.Tree.run_done]

theorem cap_historyAudit_run {S : Type} (safe : S × P → A → Prop) (marked : P → Bool)
    (step : S → P → A → S) {fuel budget : ℕ} (state : S)
    (tree : Tree P A Out fuel) (bounded : AtMost budget tree) (H : P → A) :
    (History.audit safe marked step state (cap budget tree bounded)).run H =
      (History.audit safe marked step state tree).run H := by
  induction tree generalizing budget state with
  | done _ => cases budget <;> rfl
  | query point next ih =>
      cases budget with
      | zero => exact False.elim bounded
      | succ budget =>
          simp only [cap, History.audit_query, Merkle.RandomOracle.Tree.run_query]
          by_cases hs : safe (state,point) (H point)
          · simp only [hs, if_true, Merkle.RandomOracle.Tree.run_map, ih]
          · simp only [hs, if_false, Merkle.RandomOracle.Tree.run_done]

/-- Every branch of a fresh tree is realizable by a total oracle. Thus an
all-oracle distinct-query bound supplies the structural depth bound, even
when the original syntactic fuel was much larger. -/
theorem atMost_of_distinct [DecidableEq P] [Nonempty A]
    {fuel budget : ℕ} (tree : Tree P A Out fuel) {known : P → Prop}
    (fresh : TranscriptV2.FreshOracle.FreshFrom known tree)
    (queries : ∀ H : P → A, ((queried tree H).toFinset).card ≤ budget) : AtMost budget tree := by
  induction tree generalizing budget known with
  | done _ => cases budget <;> trivial
  | query point next ih =>
      have positive : 0 < budget := by
        let H : P → A := fun _ => Classical.choice (inferInstance : Nonempty A)
        have member : point ∈ (queried (.query point next) H).toFinset := by
          simp [queried_query]
        have counted := Finset.card_pos.mpr ⟨point,member⟩
        exact counted.trans_le (queries H)
      obtain ⟨rest, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      intro answer
      apply ih answer (fresh.2 answer)
      intro H
      have absent := (fresh.2 answer).not_queried H point (Or.inl rfl)
      let changed := Function.update H point answer
      have agree : AgreeOff point H changed := by
        intro other different
        simp only [changed, Function.update_of_ne different]
      have same := run_eq_of_not_mem (next answer) point agree absent
      have trace : queried (next answer) changed = queried (next answer) H :=
        congrArg (fun result => result.2.map Prod.fst) same
      have count := queries changed
      rw [queried_query] at count
      simp only [changed, Function.update_self] at count
      rw [trace, List.toFinset_cons, Finset.card_insert_of_notMem (by simpa using absent)] at count
      omega

end Survival.QueryBudget
