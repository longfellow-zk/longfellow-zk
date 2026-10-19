import Bcs.FootprintCharging

set_option maxHeartbeats 800000

/-!
# Affine block soundness

A block guarantees an outcome bound, not a Boolean transition at every
challenge. `Certificate` is its finite-experiment interface: an intercept,
a per-unit price, and explicit nonnegative resource spending. `Sound` is
the uniform family version. Context, adversary, budgets, and outside-oracle
answers can all be included in the family index.

Composition uses an event cover and an allocation of spending. It does not
infer disjoint spending from separate bounds in the same total query budget.
`queryCost` and `queryCost_sum_le` provide the allocation for disjoint hash
domains, with arbitrary adaptive query order. No independence of failure
events is required. Product-error amplification is a different theorem.
-/

namespace Bcs.AffineBlock

open Finset FiniteProbability TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

structure Rate where
  intercept : ℚ
  slope : ℚ
  intercept_nonneg : 0 ≤ intercept
  slope_nonneg : 0 ≤ slope

def Rate.diagonal (epsilon : ℚ) (h : 0 ≤ epsilon) : Rate := ⟨epsilon, epsilon, h, h⟩

/-- The resource may be an adaptive count, or a deterministic budget.
These interpretations are not interchangeable without a separate proof. -/
structure Certificate {Omega : Type} [Fintype Omega]
    (failure : Omega → Prop) (spend : Omega → ℚ) (rate : Rate) : Prop where
  spend_nonneg : ∀ omega, 0 ≤ spend omega
  bound : density failure ≤ rate.intercept + rate.slope * average spend

/-- Uniformity over the declared experiment family is part of soundness.
In particular an outside-oracle parameter is universally quantified, not
sampled first and then used to choose a certificate. -/
def Sound {Context : Type} {Omega : Context → Type} [∀ c, Fintype (Omega c)]
    (failure : ∀ c, Omega c → Prop) (spend : ∀ c, Omega c → ℚ) (rate : Rate) : Prop :=
  ∀ c, Certificate (failure c) (spend c) rate

theorem average_add {Omega : Type} [Fintype Omega] (f g : Omega → ℚ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, sum_add_distrib, add_div]

theorem average_mul {Omega : Type} [Fintype Omega] (a : ℚ) (f : Omega → ℚ) :
    average (fun x => a * f x) = a * average f := by
  simp only [average, ← mul_sum, mul_div_assoc]

theorem density_eq_average {Omega : Type} [Fintype Omega] (event : Omega → Prop) :
    density event = average (fun x => if event x then (1 : ℚ) else 0) := by
  simp [density, average, sum_boole]

theorem Certificate.of_budget {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (failure : Omega → Prop) (rate : Rate) (budget : ℚ) (hn : 0 ≤ budget)
    (h : density failure ≤ rate.intercept + rate.slope * budget) :
    Certificate failure (fun _ => budget) rate :=
  ⟨fun _ => hn, by simpa only [average_const] using h⟩

theorem Certificate.mono_event {Omega : Type} [Fintype Omega]
    {failure covered : Omega → Prop} {spend : Omega → ℚ} {rate : Rate}
    (h : Certificate covered spend rate) (hcover : ∀ x, failure x → covered x) :
    Certificate failure spend rate :=
  ⟨h.spend_nonneg, (density_mono hcover).trans h.bound⟩

theorem Certificate.cap {Omega : Type} [Fintype Omega] [Nonempty Omega]
    {failure : Omega → Prop} {spend : Omega → ℚ} {rate : Rate}
    (h : Certificate failure spend rate) (budget : ℚ) (hcap : ∀ x, spend x ≤ budget) :
    density failure ≤ rate.intercept + rate.slope * budget := by
  have hc : average spend ≤ budget := (average_mono hcap).trans_eq (average_const budget)
  exact h.bound.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc rate.slope_nonneg))

def aggregate {Index : Type} [Fintype Index] (rates : Index → Rate)
    (kappa : ℚ) (hk : 0 ≤ kappa) : Rate :=
  ⟨∑ i, (rates i).intercept, kappa,
    sum_nonneg (fun i _ => (rates i).intercept_nonneg), hk⟩

noncomputable def maxSlope {Index : Type} [Fintype Index] [Nonempty Index]
    (rates : Index → Rate) : ℚ := univ.sup' univ_nonempty (fun i => (rates i).slope)

theorem slope_le_maxSlope {Index : Type} [Fintype Index] [Nonempty Index]
    (rates : Index → Rate) (i : Index) : (rates i).slope ≤ maxSlope rates :=
  Finset.le_sup' (fun i => (rates i).slope) (mem_univ i)

theorem maxSlope_nonneg {Index : Type} [Fintype Index] [Nonempty Index]
    (rates : Index → Rate) : 0 ≤ maxSlope rates :=
  (rates (Classical.choice inferInstance)).slope_nonneg.trans
    (slope_le_maxSlope rates (Classical.choice inferInstance))

/-- Parallel/conjunctive composition: intercepts add; a common upper bound
on local prices multiplies total spending. No independence assumption. -/
theorem parallel {Index Omega : Type} [Fintype Index] [Fintype Omega]
    (events : Index → Omega → Prop) (spend : Index → Omega → ℚ)
    (rates : Index → Rate) (cert : ∀ i, Certificate (events i) (spend i) (rates i))
    (failure : Omega → Prop) (cover : ∀ x, failure x → ∃ i, events i x)
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa) :
    Certificate failure (fun x => ∑ i, spend i x) (aggregate rates kappa hk) := by
  refine ⟨fun x => sum_nonneg (fun i _ => (cert i).spend_nonneg x), ?_⟩
  calc
    density failure ≤ ∑ i, density (events i) := density_union_le failure events cover
    _ ≤ ∑ i, ((rates i).intercept + (rates i).slope * average (spend i)) :=
      sum_le_sum fun i _ => (cert i).bound
    _ ≤ ∑ i, ((rates i).intercept + kappa * average (spend i)) := by
      apply sum_le_sum
      intro i _
      have hn : 0 ≤ average (spend i) := by
        unfold average
        exact div_nonneg (sum_nonneg fun x _ => (cert i).spend_nonneg x) (by positivity)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hprice i) hn)
    _ = _ := by simp only [aggregate, sum_add_distrib, ← mul_sum, average_sum]

/-- A Boolean boundary state is only needed for the sequential cover,
not for the block's internal challenges or charge construction. -/
theorem exists_escape {n : ℕ} (doomed : Fin (n+1) → Prop)
    (start : doomed 0) (finish : ¬ doomed (Fin.last n)) :
    ∃ i : Fin n, doomed i.castSucc ∧ ¬ doomed i.succ := by
  by_contra hn
  have step (i : Fin n) : doomed i.castSucc → doomed i.succ := by
    intro hi
    by_contra hs
    exact hn ⟨i, hi, hs⟩
  have all (i : ℕ) (hi : i ≤ n) : doomed ⟨i, by omega⟩ := by
    induction i with
    | zero => exact start
    | succ i ih => exact step ⟨i, by omega⟩ (ih (by omega))
  exact finish (all n le_rfl)

/-- Sequential composition via an escaping block. The events may depend
on the whole oracle, including future answers; their certificates must
already be valid on that same experiment. -/
theorem sequential {Omega : Type} [Fintype Omega] {n : ℕ}
    (doomed : Fin (n+1) → Omega → Prop)
    (spend : Fin n → Omega → ℚ) (rates : Fin n → Rate)
    (cert : ∀ i, Certificate (fun x => doomed i.castSucc x ∧ ¬ doomed i.succ x)
      (spend i) (rates i))
    (failure : Omega → Prop) (start : ∀ x, failure x → doomed 0 x)
    (finish : ∀ x, failure x → ¬ doomed (Fin.last n) x)
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa) :
    Certificate failure (fun x => ∑ i, spend i x) (aggregate rates kappa hk) :=
  parallel _ spend rates cert failure
    (fun x hx => exists_escape (fun i => doomed i x) (start x hx) (finish x hx))
    kappa hk hprice

/-- Contextual certificates compose pointwise, allowing statements and
failure predicates to depend on the shared binding context. -/
theorem sound_parallel {Context Index : Type} {Omega : Context → Type}
    [Fintype Index] [∀ c, Fintype (Omega c)]
    (events : ∀ c, Index → Omega c → Prop) (spend : ∀ c, Index → Omega c → ℚ)
    (rates : Index → Rate)
    (cert : ∀ i, Sound (fun c => events c i) (fun c => spend c i) (rates i))
    (failure : ∀ c, Omega c → Prop) (cover : ∀ c x, failure c x → ∃ i, events c i x)
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa) :
    Sound failure (fun c x => ∑ i, spend c i x) (aggregate rates kappa hk) :=
  fun c => parallel (events c) (spend c) rates (fun i => cert i c)
    (failure c) (cover c) kappa hk hprice

section Oracle

variable {Q C Out : Type} [DecidableEq Q]

/-- Count every prover call in this domain; repeated calls are harmless
overcounts. Verifier recomputation belongs to the intercept. -/
noncomputable def queryCost (domain : Finset Q) {N : ℕ} (tree : Tree Q C Out N)
    (H : Q → C) : ℚ :=
  match tree with
  | .done _ => 0
  | .query q next => (if q ∈ domain then 1 else 0) + queryCost domain (next (H q)) H

theorem queryCost_nonneg (domain : Finset Q) {N : ℕ} (tree : Tree Q C Out N) (H : Q → C) :
    0 ≤ queryCost domain tree H := by
  induction tree with
  | done => exact le_rfl
  | query q next ih => exact add_nonneg (by split_ifs <;> norm_num) (ih (H q))

/-- Domain ownership implies the pathwise allocation needed by composition.
The premise permits unused oracle domains but forbids double charging. -/
theorem queryCost_sum_le {Index : Type} [Fintype Index]
    (domains : Index → Finset Q)
    (ownership : ∀ q, (∑ i, if q ∈ domains i then (1 : ℚ) else 0) ≤ 1)
    {N : ℕ} (tree : Tree Q C Out N) (H : Q → C) :
    (∑ i, queryCost (domains i) tree H) ≤ N := by
  induction tree with
  | done => simp [queryCost]
  | query q next ih =>
    simp only [queryCost, sum_add_distrib, Nat.cast_add, Nat.cast_one]
    have h := add_le_add (ownership q) (ih (H q))
    simpa only [add_comm] using h

theorem ownership_of_disjoint {Index : Type} [Fintype Index]
    (domains : Index → Finset Q) (hd : Pairwise (fun i j => Disjoint (domains i) (domains j))) :
    ∀ q, (∑ i, if q ∈ domains i then (1 : ℚ) else 0) ≤ 1 := by
  intro q
  by_cases h : ∃ i, q ∈ domains i
  · obtain ⟨i, hi⟩ := h
    have he (j : Index) : q ∈ domains j ↔ j = i := by
      constructor
      · intro hj
        by_contra hn
        exact (Finset.disjoint_left.mp (hd hn)) hj hi
      · rintro rfl; exact hi
    simp_rw [he]
    simp
  · have he (i : Index) : q ∉ domains i := fun hi => h ⟨i, hi⟩
    simp [he]

theorem queryCost_biUnion {Index : Type} [Fintype Index]
    (domains : Index → Finset Q) (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    {N : ℕ} (tree : Tree Q C Out N) (H : Q → C) :
    queryCost (univ.biUnion domains) tree H = ∑ i, queryCost (domains i) tree H := by
  have he (q : Q) : (if q ∈ univ.biUnion domains then (1 : ℚ) else 0) =
      ∑ i, if q ∈ domains i then 1 else 0 := by
    by_cases h : ∃ i, q ∈ domains i
    · obtain ⟨i, hi⟩ := h
      have hm (j : Index) : q ∈ domains j ↔ j = i := by
        constructor
        · intro hj
          by_contra hn
          exact (Finset.disjoint_left.mp (hd hn)) hj hi
        · rintro rfl; exact hi
      simp [hm]
    · have hn (i : Index) : q ∉ domains i := fun hi => h ⟨i, hi⟩
      simp [hn]
  induction tree with
  | done => simp [queryCost]
  | query q next ih => simp only [queryCost, he, ih (H q), sum_add_distrib]

variable [Fintype Q] [Fintype C] [Nonempty C]

/-- The oracle-specialized definition quantifies over arbitrary adversary
trees on the full hash domain. A local-domain certificate is stronger than
a theorem stated only in the adversary's total fuel. -/
def OracleSound (domain : Finset Q) (failure : Out → (Q → C) → Prop) (rate : Rate) : Prop :=
  ∀ (N : ℕ) (tree : Tree Q C Out N),
    Certificate (fun H => failure (tree.run H).1 H) (queryCost domain tree) rate

omit [Nonempty C] in
/-- Closure of the interface itself, so the composite can be nested as a
single block. Its domain is the union of the component domains. -/
theorem oracle_parallel_certificate {Index : Type} [Fintype Index]
    (domains : Index → Finset Q) (events : Index → Out → (Q → C) → Prop)
    (rates : Index → Rate) (cert : ∀ i, OracleSound (domains i) (events i) (rates i))
    (failure : Out → (Q → C) → Prop)
    (cover : ∀ out H, failure out H → ∃ i, events i out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa) :
    OracleSound (univ.biUnion domains) failure (aggregate rates kappa hk) := by
  intro N tree
  have h := parallel (fun i H => events i (tree.run H).1 H)
    (fun i => queryCost (domains i) tree) rates (fun i => cert i N tree)
    (fun H => failure (tree.run H).1 H) (fun H => cover (tree.run H).1 H)
    kappa hk hprice
  have he : queryCost (univ.biUnion domains) tree = fun H => ∑ i, queryCost (domains i) tree H :=
    funext (queryCost_biUnion domains hd tree)
  rw [he]
  exact h

omit [Nonempty C] in
theorem oracle_sequential_certificate {n : ℕ}
    (domains : Fin n → Finset Q) (doomed : Fin (n+1) → Out → (Q → C) → Prop)
    (rates : Fin n → Rate)
    (cert : ∀ i, OracleSound (domains i)
      (fun out H => doomed i.castSucc out H ∧ ¬ doomed i.succ out H) (rates i))
    (failure : Out → (Q → C) → Prop)
    (start : ∀ out H, failure out H → doomed 0 out H)
    (finish : ∀ out H, failure out H → ¬ doomed (Fin.last n) out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa) :
    OracleSound (univ.biUnion domains) failure (aggregate rates kappa hk) :=
  oracle_parallel_certificate domains _ rates cert failure
    (fun out H hf => exists_escape (fun i => doomed i out H) (start out H hf) (finish out H hf))
    hd kappa hk hprice

theorem oracle_parallel {Index : Type} [Fintype Index]
    (domains : Index → Finset Q) (events : Index → Out → (Q → C) → Prop)
    (rates : Index → Rate) (cert : ∀ i, OracleSound (domains i) (events i) (rates i))
    (failure : Out → (Q → C) → Prop)
    (cover : ∀ out H, failure out H → ∃ i, events i out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa)
    {N : ℕ} (tree : Tree Q C Out N) :
    density (fun H => failure (tree.run H).1 H) ≤ (∑ i, (rates i).intercept) + N*kappa := by
  have h := parallel (fun i H => events i (tree.run H).1 H)
    (fun i => queryCost (domains i) tree) rates (fun i => cert i N tree)
    (fun H => failure (tree.run H).1 H) (fun H => cover (tree.run H).1 H)
    kappa hk hprice
  have hb := h.cap (N : ℚ) (queryCost_sum_le domains (ownership_of_disjoint domains hd) tree)
  simpa only [aggregate, mul_comm] using hb

theorem oracle_parallel_max {Index : Type} [Fintype Index] [Nonempty Index]
    (domains : Index → Finset Q) (events : Index → Out → (Q → C) → Prop)
    (rates : Index → Rate) (cert : ∀ i, OracleSound (domains i) (events i) (rates i))
    (failure : Out → (Q → C) → Prop)
    (cover : ∀ out H, failure out H → ∃ i, events i out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    {N : ℕ} (tree : Tree Q C Out N) :
    density (fun H => failure (tree.run H).1 H) ≤
      (∑ i, (rates i).intercept) + N*maxSlope rates :=
  oracle_parallel domains events rates cert failure cover hd (maxSlope rates)
    (maxSlope_nonneg rates) (slope_le_maxSlope rates) tree

theorem oracle_sequential {n : ℕ}
    (domains : Fin n → Finset Q) (doomed : Fin (n+1) → Out → (Q → C) → Prop)
    (rates : Fin n → Rate)
    (cert : ∀ i, OracleSound (domains i)
      (fun out H => doomed i.castSucc out H ∧ ¬ doomed i.succ out H) (rates i))
    (failure : Out → (Q → C) → Prop)
    (start : ∀ out H, failure out H → doomed 0 out H)
    (finish : ∀ out H, failure out H → ¬ doomed (Fin.last n) out H)
    (hd : Pairwise (fun i j => Disjoint (domains i) (domains j)))
    (kappa : ℚ) (hk : 0 ≤ kappa) (hprice : ∀ i, (rates i).slope ≤ kappa)
    {N : ℕ} (tree : Tree Q C Out N) :
    density (fun H => failure (tree.run H).1 H) ≤ (∑ i, (rates i).intercept) + N*kappa :=
  oracle_parallel domains _ rates cert failure
    (fun out H hf => exists_escape (fun i => doomed i out H) (start out H hf) (finish out H hf))
    hd kappa hk hprice tree

omit [Fintype Q] [Fintype C] [Nonempty C] in
private theorem activated_cost_le {Index : Type} [Fintype Index] {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) (domain : Finset Q)
    (support : Index → Finset Q) (budget : Index → ℚ) (rate : Rate)
    (hn : ∀ i, 0 ≤ budget i)
    (hquery : ∀ q, (∑ i, if q ∈ support i then budget i else 0) ≤
      rate.slope * (if q ∈ domain then 1 else 0))
    (hfinal : ∀ out, (∑ i, if point out ∈ support i then budget i else 0) ≤ rate.intercept)
    (H : Q → C) :
    (∑ i, if hits (appendFinalQuery tree point) H (support i) then budget i else 0) ≤
      rate.intercept + rate.slope * queryCost domain tree H := by
  induction tree with
  | done out =>
    simpa [appendFinalQuery, Tree.bind, hits_weakenAdd, hits, queryCost] using hfinal out
  | query q next ih =>
    have hs :
        (∑ i, if hits (appendFinalQuery (.query q next) point) H (support i) then budget i else 0) ≤
          (∑ i, if q ∈ support i then budget i else 0) +
          ∑ i, if hits (appendFinalQuery (next (H q)) point) H (support i) then budget i else 0 := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro i _
      by_cases hq : q ∈ support i
      · simp only [appendFinalQuery, Tree.bind, hits, if_pos hq, ↓reduceIte]
        split_ifs <;> linarith [hn i]
      · simp only [appendFinalQuery, Tree.bind, hits, if_neg hq, zero_add]
        exact le_rfl
    have h := hs.trans (add_le_add (hquery q) (ih (H q)))
    simpa only [queryCost, mul_add, add_assoc, add_left_comm] using h

/-- First-hit/footprint charging discharges the strong local-domain
certificate. Local means alone are insufficient: the shared-query load
and final verifier load are explicit premises. -/
theorem of_footprints {Index : Type} [Fintype Index] {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) (domain : Finset Q)
    (support : Index → Finset Q) (weight : Index → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ)
    (failure : (Q → C) → Prop) (rate : Rate)
    (hweight : ∀ i H, 0 ≤ weight i H) (hbudget : ∀ i off, 0 ≤ budget i off)
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i off)
    (hquery : ∀ (H : Q → C) q, (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤
      rate.slope * (if q ∈ domain then 1 else 0))
    (hfinal : ∀ (H : Q → C) out, (∑ i, if point out ∈ support i then budget i (fun z => H z.1) else 0) ≤
      rate.intercept)
    (hcover : ∀ H, failure H → ∃ i, point (tree.run H).1 ∈ support i ∧ 1 ≤ weight i H) :
    Certificate failure (queryCost domain tree) rate := by
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  have hc : ∀ H, failure H → 1 ≤ ∑ i,
      if hits (appendFinalQuery tree point) H (support i) then weight i H else 0 := by
    intro H hf
    obtain ⟨i, hi, hw⟩ := hcover H hf
    have hh := hits_of_mem (appendFinalQuery tree point) H (support i) (point (tree.run H).1)
      (appendFinalQuery_mem tree point H) hi
    have hn (j : Index) : 0 ≤ (if hits (appendFinalQuery tree point) H (support j) then weight j H else 0) := by
      split_ifs
      · exact hweight j H
      · exact le_rfl
    exact hw.trans (by simpa [hh] using single_le_sum (fun j _ => hn j) (mem_univ i))
  have hp := event_le_expected_budget (appendFinalQuery tree point) support weight budget
    failure hweight hlocal hc
  have ha := average_mono fun H : Q → C => activated_cost_le tree point domain support
    (fun i => budget i (fun z => H z.1)) rate (fun i => hbudget i _) (hquery H) (hfinal H) H
  have h := hp.trans ha
  simpa only [average_add, average_const, average_mul] using h

/-- Uniform outside-oracle bounds can be integrated without assuming that
the adversary explores the block before or after the other domains. -/
theorem of_outside (domain : Finset Q) (failure : (Q → C) → Prop)
    (spend : (Q → C) → ℚ) (rate : Rate) (hn : ∀ H, 0 ≤ spend H)
    (h : ∀ off : Outside domain → C,
      Certificate (fun on : Inside domain → C => failure ((split domain).symm (on, off)))
        (fun on => spend ((split domain).symm (on, off))) rate) :
    Certificate failure spend rate := by
  refine ⟨hn, ?_⟩
  rw [density_eq_average, average_split domain]
  have hs := average_mono fun off => (h off).bound
  simp_rw [density_eq_average] at hs
  rw [average_add, average_const, average_mul] at hs
  simpa only [← average_split domain] using hs

end Oracle
end Bcs.AffineBlock
