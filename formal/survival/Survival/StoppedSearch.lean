import Survival.QueryBudget

/-! The existing chronological audit, viewed through the reached transparent
and opaque query counts. The escape query is included. These linear accounting
laws have no restriction of the form `rate * queries ≤ 1`. -/
noncomputable section
namespace Survival.StoppedSearch
open Finset Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open scoped Classical

variable {P A Out S : Type}

/-- Mathematical observation of an existing tree's run. Query names, answers,
branches and trace are unchanged; only the return value also records the trace. -/
private def observe : {fuel : ℕ} → Tree P A Out fuel → Tree P A (Out × List (P × A)) fuel
  | _, .done output => .done (output,[])
  | _, .query point next => .query point fun answer =>
      (observe (next answer)).map fun result => (result.1,(point,answer)::result.2)

private theorem observe_run {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (observe tree).run H = (tree.run H,(tree.run H).2) := by
  induction tree with
  | done output => rfl
  | query point next ih => simp only [observe, Tree.run_query, Tree.run_map, ih]

private theorem observe_fresh [DecidableEq P] {fuel : ℕ} (tree : Tree P A Out fuel)
    {known : P → Prop} (fresh : FreshOracle.FreshFrom known tree) :
    FreshOracle.FreshFrom known (observe tree) := by
  induction tree generalizing known with
  | done output => trivial
  | query point next ih => exact ⟨fresh.1,fun answer => Hybrid.fresh_map _ _ (ih answer (fresh.2 answer))⟩

variable [Fintype A] [Nonempty A]

private def traceMean (value : Out × List (P × A) → ℚ) {fuel : ℕ} (tree : Tree P A Out fuel) : ℚ :=
  FreshOracle.mean value (observe tree)

omit [Nonempty A] in
private theorem traceMean_map {X : Type} (f : Out → X) (value : X × List (P × A) → ℚ)
    {fuel : ℕ} (tree : Tree P A Out fuel) :
    traceMean value (tree.map f) = traceMean (fun result => value (f result.1,result.2)) tree := by
  induction tree generalizing value with
  | done output => rfl
  | query point next ih =>
      simp only [traceMean, observe, Merkle.RandomOracle.Tree.map, FreshOracle.mean, Hybrid.mean_map] at ih ⊢
      exact congrArg (fun x : ℚ => x/Fintype.card A) (sum_congr rfl (fun answer _ => ih answer _))

omit [Nonempty A] in
private theorem traceMean_query (value : Out × List (P × A) → ℚ)
    {fuel : ℕ} (point : P) (next : A → Tree P A Out fuel) :
    traceMean value (.query point next) =
      (∑ answer, traceMean (fun result => value (result.1,(point,answer)::result.2)) (next answer)) /
        Fintype.card A := by
  simp only [traceMean,observe,FreshOracle.mean,Hybrid.mean_map]

omit [Nonempty A] in
private theorem traceMean_add (first second : Out × List (P × A) → ℚ)
    {fuel : ℕ} (tree : Tree P A Out fuel) :
    traceMean (fun result => first result + second result) tree =
      traceMean first tree + traceMean second tree := Hybrid.mean_add first second (observe tree)

private theorem traceMean_const (value : ℚ) {fuel : ℕ} (tree : Tree P A Out fuel) :
    traceMean (fun _ => value) tree = value := Hybrid.mean_const value (observe tree)

private theorem traceMean_law [Fintype P] [DecidableEq P]
    (value : Out × List (P × A) → ℚ) {fuel : ℕ} (tree : Tree P A Out fuel)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree) :
    (∑ H : P → A, value (tree.run H))/Fintype.card (P → A) = traceMean value tree := by
  have law := FreshOracle.uniform_mean value (observe tree) (observe_fresh tree fresh)
  simpa only [observe_run,Fintype.card_fun,Nat.cast_pow,traceMean] using law

/-- The existing audit already returns K. J is the remaining reached trace
length, so the final transparent query that triggers escape is included. -/
def transparent (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A) : ℕ :=
  ((History.audit safe marked step state tree).run H).2.length -
    ((History.audit safe marked step state tree).run H).1.2

omit [Fintype A] [Nonempty A] in
theorem counts_eq (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) (H : P → A) :
    transparent safe marked step state tree H + ((History.audit safe marked step state tree).run H).1.2 =
      ((History.audit safe marked step state tree).run H).2.length := by
  unfold transparent
  apply Nat.sub_add_cancel
  rw [History.audit_count]
  exact List.length_filter_le _ _

omit [Fintype A] [Nonempty A] in
private theorem length_le {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (tree.run H).2.length ≤ fuel := by
  induction tree with
  | done output => simp
  | query point next ih => simpa only [Tree.run_query,List.length_cons] using Nat.succ_le_succ (ih (H point))

omit [Fintype A] in
/-- The two reached-query classes spend the original distinct-query budget. -/
theorem counts_le_support [DecidableEq P]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    {fuel queries : ℕ} (state : S) (tree : Tree P A Out fuel)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (bounded : ∀ H, (seen tree H).card ≤ queries) (H : P → A) :
    transparent safe marked step state tree H + ((History.audit safe marked step state tree).run H).1.2 ≤ queries := by
  rw [counts_eq]
  have depth := QueryBudget.atMost_of_distinct tree fresh bounded
  have bound := length_le (History.audit safe marked step state (QueryBudget.cap queries tree depth)) H
  simpa only [QueryBudget.cap_historyAudit_run] using bound

private def balance (rate : ℚ) (result : (Bool × ℕ) × List (P × A)) : ℚ :=
  indicator result.1.1 + rate*result.1.2 - rate*result.2.length

omit [Fintype A] [Nonempty A] in
private theorem balance_eq (rate : ℚ) (result : (Bool × ℕ) × List (P × A)) (transparent : ℕ)
    (counts : transparent + result.1.2 = result.2.length) :
    balance rate result = (if result.1.1 = true then (1 : ℚ) else 0) - rate*transparent := by
  have castCounts : (transparent : ℚ) + result.1.2 = result.2.length := by exact_mod_cast counts
  unfold balance indicator
  rw [← castCounts]
  cases result.1.1 <;> simp only [if_true,Bool.false_eq_true,if_false] <;> ring

omit [Fintype A] [Nonempty A] in
private theorem integrate_balance {Omega : Type} [Fintype Omega]
    (rate : ℚ) (outcome : Omega → (Bool × ℕ) × List (P × A)) (transparent : Omega → ℕ)
    (counts : ∀ h, transparent h + (outcome h).1.2 = (outcome h).2.length)
    (mean : (∑ h, balance rate (outcome h))/Fintype.card Omega ≤ 0) :
    density (fun h => (outcome h).1.1 = true) ≤
      rate*((∑ h, (transparent h : ℚ))/Fintype.card Omega) := by
  have values (h : Omega) : balance rate (outcome h) =
      (if (outcome h).1.1 = true then (1 : ℚ) else 0) - rate*(transparent h : ℚ) :=
    balance_eq rate _ _ (counts h)
  simp_rw [values] at mean
  rw [sum_sub_distrib,← mul_sum,sub_div,mul_div_assoc] at mean
  have indicator_mean :
      (∑ h, if (outcome h).1.1 = true then (1 : ℚ) else 0)/Fintype.card Omega =
        density (fun h => (outcome h).1.1 = true) := by
    rw [FiniteCover.density_indicator]
    congr 1
    apply sum_congr rfl
    intro h _
    cases (outcome h).1.1 <;> simp only [Bool.false_eq_true,if_false,if_true]
  rw [indicator_mean] at mean
  exact sub_nonpos.mp mean

private theorem balance_mean_le (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S)
    (rate : ℚ)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false → density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel) :
    traceMean (balance rate) (History.audit safe marked step state tree) ≤ 0 := by
  induction tree generalizing state with
  | done output => simp [History.audit,History.enrich,Hybrid.audit,mapQueries,traceMean,observe,FreshOracle.mean,balance,indicator]
  | query point next ih =>
      rw [History.audit_query,traceMean_query]
      have each (answer : A) :
          traceMean (fun result => balance rate (result.1,(point,answer)::result.2))
            (if safe (state,point) answer then
              (History.audit safe marked step (step state point answer) (next answer)).map
                (fun result => (result.1,result.2+if marked point then 1 else 0))
             else .done (true,if marked point then 1 else 0)) ≤
          (if ¬safe (state,point) answer then (1 : ℚ) else 0) + (if marked point then 0 else -rate) := by
        by_cases survives : safe (state,point) answer
        · simp only [survives,if_true,not_true_eq_false,if_false,zero_add,traceMean_map]
          have values : (fun result : (Bool × ℕ) × List (P × A) =>
              balance rate ((result.1.1,result.1.2+if marked point then 1 else 0),(point,answer)::result.2)) =
              fun result => balance rate result + (if marked point then 0 else -rate) := by
            funext result
            cases marked point <;> simp [balance, Nat.cast_add, Nat.cast_one, List.length_cons] <;> ring
          rw [values,traceMean_add,traceMean_const]
          linarith [ih answer (step state point answer)]
        · simp only [survives,if_false,not_false_eq_true,if_true]
          cases marked point <;> simp [traceMean,observe,FreshOracle.mean,balance,indicator]
      have averaged := div_le_div_of_nonneg_right (sum_le_sum (s := univ) (fun answer _ => each answer))
        (show (0 : ℚ) ≤ Fintype.card A by positivity)
      have denom : (Fintype.card A : ℚ) ≠ 0 := by positivity
      have expression :
          (∑ answer : A, ((if ¬safe (state,point) answer then (1 : ℚ) else 0) +
            (if marked point then 0 else -rate)))/Fintype.card A =
          density (fun answer => ¬safe (state,point) answer) + (if marked point then 0 else -rate) := by
        rw [sum_add_distrib,add_div,FiniteCover.density_indicator]
        simp only [sum_const,card_univ,nsmul_eq_mul,mul_div_cancel_left₀ _ denom]
        apply congrArg (fun total : ℚ => total/Fintype.card A + (if marked point then 0 else -rate))
        apply sum_congr rfl
        intro answer _
        by_cases survives : safe (state,point) answer <;> simp only [survives,not_true_eq_false,not_false_eq_true,if_true,if_false]
      rw [expression] at averaged
      apply averaged.trans
      cases flag : marked point with
      | false => simpa only [flag,Bool.false_eq_true,if_false,sub_eq_add_neg] using sub_nonpos.mpr (hazard state point flag)
      | true => simp [density,opaque_safe state point flag]

/-- Chronological escape costs at most p times the expected number J of
transparent queries actually reached. This holds for every query budget. -/
theorem escape_le [Fintype P] [DecidableEq P]
    (safe : S × P → A → Prop) (marked : P → Bool) (step : S → P → A → S) (rate : ℚ)
    (opaque_safe : ∀ state point, marked point = true → ∀ answer, safe (state,point) answer)
    (hazard : ∀ state point, marked point = false → density (fun answer => ¬safe (state,point) answer) ≤ rate)
    {fuel : ℕ} (state : S) (tree : Tree P A Out fuel)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree) :
    density (fun H => ((History.audit safe marked step state tree).run H).1.1 = true) ≤
      rate*((∑ H : P → A, (transparent safe marked step state tree H : ℚ))/Fintype.card (P → A)) := by
  apply integrate_balance rate (fun H => (History.audit safe marked step state tree).run H)
    (transparent safe marked step state tree) (counts_eq safe marked step state tree)
  exact (traceMean_law (balance rate) (History.audit safe marked step state tree)
    (History.audit_fresh safe marked step state tree fresh)).trans_le
      (balance_mean_le safe marked step rate opaque_safe hazard state tree)

end Survival.StoppedSearch
