import Bcs.FinalQuery
import Bcs.PotentialOracle
import Bcs.FiniteProbability

/-!
# First-hit charging for finite sets of oracle coordinates

A certificate may inspect several fresh answers jointly. Its activation is
the first query to its footprint, which is independent of all answers in
that footprint. Local budgets may depend on the complementary oracle.

The incidence bound is essential: all certificates containing a queried
point must share that point's budget. It is not implied by a bound for each
certificate separately. The final verifier lookup has its own budget, so
the result is affine even for a prover making no queries.
-/

set_option autoImplicit false

namespace Bcs.TotalOracle.Footprint

open Finset Merkle.RandomOracle
open scoped Classical

noncomputable def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card A

theorem average_mono {A : Type} [Fintype A] {f g : A → ℚ}
    (h : ∀ a, f a ≤ g a) : average f ≤ average g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

@[simp] theorem average_const {A : Type} [Fintype A] [Nonempty A] (c : ℚ) :
    average (fun _ : A => c) = c := by
  have h : (Fintype.card A : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [average, h]

theorem average_sum {A I : Type} [Fintype A] [Fintype I] (f : I → A → ℚ) :
    average (fun a => ∑ i, f i a) = ∑ i, average (f i) := by
  simp only [average, ← Finset.sum_div]
  rw [Finset.sum_comm]

/-- An individual coordinate of a uniform finite function is uniform. -/
theorem average_eval {A C : Type} [Fintype A] [DecidableEq A]
    [Fintype C] [Nonempty C] (a : A) (f : C → ℚ) :
    average (fun H : A → C => f (H a)) = average f := by
  have h := sum_coord_mul_rat a (fun _ c => f c) (by intros; rfl)
  have hc : (Fintype.card C : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ha : (Fintype.card (A → C) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [sum_const, card_univ, nsmul_eq_mul] at h
  unfold average
  apply (div_eq_div_iff ha hc).mpr
  simpa [mul_comm] using h

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

abbrev Inside (s : Finset Q) := {q : Q // q ∈ s}
abbrev Outside (s : Finset Q) := {q : Q // q ∉ s}

def split (s : Finset Q) :
    (Q → C) ≃ ((Inside s → C) × (Outside s → C)) :=
  Equiv.piEquivPiSubtypeProd (fun q => q ∈ s) (fun _ => C)

omit [Nonempty C] in
theorem average_split (s : Finset Q) (f : (Q → C) → ℚ) :
    average f = average (fun off : Outside s → C =>
      average (fun on : Inside s → C => f ((split s).symm (on, off)))) := by
  have hc := Fintype.card_congr (split (C := C) s)
  have hs := Fintype.sum_equiv (split (C := C) s) f
    (fun p => f ((split s).symm p)) (by intro H; simp)
  unfold average
  rw [hs, hc]
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

/-- Whether an execution touches a footprint, before reading its first answer. -/
def hits {Out : Type} {N : ℕ} (tree : Tree Q C Out N)
    (H : Q → C) (s : Finset Q) : Bool :=
  match tree with
  | .done _ => false
  | .query q next => if q ∈ s then true else hits (next (H q)) H s

omit [Fintype Q] [Fintype C] [Nonempty C] in
theorem hits_off {Out : Type} {N : ℕ} (tree : Tree Q C Out N)
    (H H' : Q → C) (s : Finset Q) (h : ∀ q, q ∉ s → H q = H' q) :
    hits tree H s = hits tree H' s := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
      by_cases hq : q ∈ s
      · simp [hits, hq]
      · simp only [hits, if_neg hq, h q hq]
        exact ih (H' q)

omit [Fintype Q] [Fintype C] [Nonempty C] in
theorem hits_of_mem {Out : Type} {N : ℕ} (tree : Tree Q C Out N)
    (H : Q → C) (s : Finset Q) (q : Q)
    (hq : q ∈ queried tree H) (hs : q ∈ s) : hits tree H s = true := by
  induction tree with
  | done _ => simp [queried] at hq
  | query x next ih =>
      by_cases hx : x ∈ s
      · simp [hits, hx]
      · rw [queried_query, List.mem_cons] at hq
        rcases hq with hq | hq
        · exact (hx (hq ▸ hs)).elim
        · simpa [hits, hx] using ih (H x) hq

/-- Fubini with the entire footprint held out. No query-order assumption. -/
theorem activated_average_le {Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (s : Finset Q) (weight : (Q → C) → ℚ)
    (budget : (Outside s → C) → ℚ)
    (hlocal : ∀ off, average (fun on => weight ((split s).symm (on, off))) ≤ budget off) :
    average (fun H => if hits tree H s then weight H else 0) ≤
      average (fun H => if hits tree H s then budget (fun q => H q.1) else 0) := by
  rw [average_split s, average_split s]
  apply average_mono
  intro off
  let base : Q → C := (split s).symm (fun _ => Classical.choice inferInstance, off)
  have hh (on : Inside s → C) : hits tree ((split s).symm (on, off)) s = hits tree base s := by
    apply hits_off
    intro q hq
    simp [base, split, Equiv.piEquivPiSubtypeProd, hq]
  have ho (on : Inside s → C) :
      (fun q : Outside s => (split s).symm (on, off) q.1) = off := by
    funext q
    simp [split, Equiv.piEquivPiSubtypeProd, q.property]
  simp_rw [hh, ho]
  cases hits tree base s with
  | false => simp
  | true => simpa only [↓reduceIte, average_const] using hlocal off

omit [Fintype Q] [Fintype C] [Nonempty C] in
@[simp] theorem hits_weaken {Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (H : Q → C) (s : Finset Q) :
    hits tree.weaken H s = hits tree H s := by
  induction tree with
  | done _ => rfl
  | query q next ih => simp [Tree.weaken, hits, ih]

omit [Fintype Q] [Fintype C] [Nonempty C] in
@[simp] theorem hits_weakenAdd {Out : Type} {N : ℕ} (n : ℕ)
    (tree : Tree Q C Out N) (H : Q → C) (s : Finset Q) :
    hits (tree.weakenAdd n) H s = hits tree H s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Tree.weakenAdd, hits_weaken, ih]

variable {I Out : Type} [Fintype I]

/-- The probabilistic part of the compiler, before any pathwise accounting.
This is the interface for an amortized proof: it must bound the expectation
of the *activated* outside budgets, not the unselected mean of each budget.
The execution can include any verifier replay, not just one final lookup. -/
theorem event_le_expected_budget {N : ℕ} (tree : Tree Q C Out N)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ)
    (failure : (Q → C) → Prop)
    (hweight : ∀ i H, 0 ≤ weight i H)
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i off)
    (hcover : ∀ H, failure H → 1 ≤ ∑ i,
      if hits tree H (support i) then weight i H else 0) :
    Bcs.FiniteProbability.density failure ≤ average (fun H => ∑ i,
      if hits tree H (support i) then budget i (fun z => H z.1) else 0) := by
  classical
  have hp (H : Q → C) : (if failure H then (1 : ℚ) else 0) ≤
      ∑ i, if hits tree H (support i) then weight i H else 0 := by
    by_cases hf : failure H
    · simpa only [hf, ↓reduceIte] using hcover H hf
    · simp only [hf, ↓reduceIte]
      exact sum_nonneg fun i _ => by split_ifs <;> simp_all
  calc
    Bcs.FiniteProbability.density failure = average (fun H => if failure H then 1 else 0) := by
      simp only [Bcs.FiniteProbability.density, average, Finset.natCast_card_filter]
    _ ≤ average (fun H => ∑ i, if hits tree H (support i) then weight i H else 0) :=
      average_mono hp
    _ ≤ _ := by
      rw [average_sum, average_sum]
      exact sum_le_sum fun i _ =>
        activated_average_le tree (support i) (weight i) (budget i) (hlocal i)

omit [Fintype Q] [Fintype C] [Nonempty C] in
/-- The pathwise accounting step. The prover uses at most `N` calls; the
one appended verifier lookup has the separate intercept budget. Repeated
queries are harmless overcounts. -/
theorem activated_budget_le {N : ℕ} (tree : Tree Q C Out N) (point : Out → Q)
    (support : I → Finset Q) (budget : I → ℚ) (epsilon kappa : ℚ)
    (hnonneg : ∀ i, 0 ≤ budget i) (hkappa : 0 ≤ kappa)
    (hquery : ∀ q, (∑ i, if q ∈ support i then budget i else 0) ≤ kappa)
    (hfinal : ∀ out, (∑ i, if point out ∈ support i then budget i else 0) ≤ epsilon)
    (H : Q → C) :
    (∑ i, if hits (appendFinalQuery tree point) H (support i) then budget i else 0) ≤
      epsilon + N * kappa := by
  induction tree with
  | @done fuel out =>
      have hf := hfinal out
      simp only [appendFinalQuery, Tree.bind, hits_weakenAdd, hits] at *
      have hn : (0 : ℚ) ≤ fuel * kappa := mul_nonneg (Nat.cast_nonneg _) hkappa
      convert hf.trans (le_add_of_nonneg_right hn) using 1
      congr 1
      apply sum_congr rfl
      intro i _
      by_cases hi : point out ∈ support i <;> simp [hi]
  | @query n q next ih =>
      have hstep :
          (∑ i, if hits (appendFinalQuery (.query q next) point) H (support i) then budget i else 0) ≤
          (∑ i, if q ∈ support i then budget i else 0) +
            ∑ i, if hits (appendFinalQuery (next (H q)) point) H (support i) then budget i else 0 := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        by_cases hq : q ∈ support i
        · simp only [appendFinalQuery, Tree.bind, hits, if_pos hq, ↓reduceIte]
          split_ifs <;> linarith [hnonneg i]
        · simp only [appendFinalQuery, Tree.bind, hits, if_neg hq, zero_add]
          exact le_rfl
      have hi := ih (H q)
      have hq := hquery q
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith

/-- A sufficient amortization rule. Activated child budgets must be paid
pathwise by a constant and *once-activated* parent potentials. Those parent
potentials may then be averaged at their own first hits. This premise is a
consumption/reuse bound; an unselected mean envelope does not imply it. -/
theorem event_le_of_parent_charge {J : Type} [Fintype J] {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ)
    (parentSupport : J → Finset Q) (potential : J → (Q → C) → ℚ)
    (parentBudget : J → ℚ) (failure : (Q → C) → Prop)
    (base epsilon kappa : ℚ)
    (hweight : ∀ i H, 0 ≤ weight i H)
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i off)
    (hcover : ∀ H, failure H → 1 ≤ ∑ i,
      if hits (appendFinalQuery tree point) H (support i) then weight i H else 0)
    (hcharge : ∀ H,
      (∑ i, if hits (appendFinalQuery tree point) H (support i)
        then budget i (fun z => H z.1) else 0) ≤
      base + ∑ j, if hits (appendFinalQuery tree point) H (parentSupport j)
        then potential j H else 0)
    (hparent : ∀ j off, average (fun on =>
      potential j ((split (parentSupport j)).symm (on, off))) ≤ parentBudget j)
    (hnonneg : ∀ j, 0 ≤ parentBudget j) (hkappa : 0 ≤ kappa)
    (hquery : ∀ q, (∑ j, if q ∈ parentSupport j then parentBudget j else 0) ≤ kappa)
    (hfinal : ∀ out,
      (∑ j, if point out ∈ parentSupport j then parentBudget j else 0) ≤ epsilon) :
    Bcs.FiniteProbability.density failure ≤ base + epsilon + N * kappa := by
  have hadd {A : Type} [Fintype A] [Nonempty A] (c : ℚ) (f : A → ℚ) :
      average (fun a => c + f a) = c + average f := by
    simp only [average, sum_add_distrib, add_div]
    rw [show (∑ _a : A, c) / (Fintype.card A : ℚ) = c from average_const c]
  calc
    Bcs.FiniteProbability.density failure ≤ average (fun H => ∑ i,
        if hits (appendFinalQuery tree point) H (support i)
          then budget i (fun z => H z.1) else 0) :=
      event_le_expected_budget (appendFinalQuery tree point) support weight budget
        failure hweight hlocal hcover
    _ ≤ average (fun H => base + ∑ j,
        if hits (appendFinalQuery tree point) H (parentSupport j) then potential j H else 0) :=
      average_mono hcharge
    _ = base + ∑ j, average (fun H =>
        if hits (appendFinalQuery tree point) H (parentSupport j) then potential j H else 0) := by
      rw [hadd, average_sum]
    _ ≤ base + ∑ j, average (fun H =>
        if hits (appendFinalQuery tree point) H (parentSupport j) then parentBudget j else 0) := by
      apply add_le_add le_rfl
      exact sum_le_sum fun j _ => activated_average_le (appendFinalQuery tree point)
        (parentSupport j) (potential j) (fun _ => parentBudget j) (hparent j)
    _ = base + average (fun H => ∑ j,
        if hits (appendFinalQuery tree point) H (parentSupport j) then parentBudget j else 0) := by
      rw [average_sum]
    _ ≤ base + average (fun _ : Q → C => epsilon + N * kappa) := by
      apply add_le_add le_rfl
      exact average_mono (activated_budget_le tree point parentSupport parentBudget
        epsilon kappa hnonneg hkappa hquery hfinal)
    _ = _ := by rw [average_const]; ring

/-- An affine FS bound allowing a unit of payment to be split among several
activated fractional certificates. -/
theorem event_le {N : ℕ} (tree : Tree Q C Out N) (point : Out → Q)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ)
    (failure : (Q → C) → Prop) (epsilon kappa : ℚ)
    (hweight : ∀ i H, 0 ≤ weight i H)
    (hbudget : ∀ i off, 0 ≤ budget i off) (hkappa : 0 ≤ kappa)
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i off)
    (hquery : ∀ (H : Q → C) q,
      (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤ kappa)
    (hfinal : ∀ (H : Q → C) out,
      (∑ i, if point out ∈ support i then budget i (fun z => H z.1) else 0) ≤ epsilon)
    (hcover : ∀ H, failure H → 1 ≤ ∑ i,
      if hits (appendFinalQuery tree point) H (support i) then weight i H else 0) :
    Bcs.FiniteProbability.density failure ≤ epsilon + N * kappa := by
  classical
  let extended := appendFinalQuery tree point
  have hp (H : Q → C) : (if failure H then (1 : ℚ) else 0) ≤
      ∑ i, if hits extended H (support i) then weight i H else 0 := by
    have hn (i : I) : 0 ≤ (if hits extended H (support i) then weight i H else 0) := by
      split_ifs
      · exact hweight i H
      · exact le_rfl
    by_cases hf : failure H
    · simpa only [hf, ↓reduceIte] using hcover H hf
    · simpa [hf] using sum_nonneg (fun i _ => hn i)
  calc
    Bcs.FiniteProbability.density failure = average (fun H => if failure H then 1 else 0) := by
      simp only [Bcs.FiniteProbability.density, average, Finset.natCast_card_filter]
    _ ≤ average (fun H => ∑ i, if hits extended H (support i) then weight i H else 0) :=
      average_mono hp
    _ ≤ average (fun H => ∑ i, if hits extended H (support i) then budget i (fun z => H z.1) else 0) := by
      rw [average_sum, average_sum]
      exact sum_le_sum fun i _ => activated_average_le extended (support i) (weight i) (budget i) (hlocal i)
    _ ≤ average (fun _ : Q → C => epsilon + N * kappa) :=
      average_mono fun H => activated_budget_le tree point support
        (fun i => budget i (fun z => H z.1)) epsilon kappa
        (fun i => hbudget i _) hkappa (hquery H) (hfinal H) H
    _ = _ := average_const _

/-- Selected-candidate specialization. A failing output identifies one
unit-paying certificate containing the designated final lookup. Selection
may depend on the whole adaptive execution, in either query order. -/
theorem selected_event_le {N : ℕ} (tree : Tree Q C Out N) (point : Out → Q)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ)
    (failure : (Q → C) → Prop) (epsilon kappa : ℚ)
    (hweight : ∀ i H, 0 ≤ weight i H)
    (hbudget : ∀ i off, 0 ≤ budget i off) (hkappa : 0 ≤ kappa)
    (hlocal : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on, off))) ≤ budget i off)
    (hquery : ∀ (H : Q → C) q,
      (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤ kappa)
    (hfinal : ∀ (H : Q → C) out,
      (∑ i, if point out ∈ support i then budget i (fun z => H z.1) else 0) ≤ epsilon)
    (hcover : ∀ H, failure H → ∃ i,
      point (tree.run H).1 ∈ support i ∧ 1 ≤ weight i H) :
    Bcs.FiniteProbability.density failure ≤ epsilon + N * kappa := by
  apply event_le tree point support weight budget failure epsilon kappa
    hweight hbudget hkappa hlocal hquery hfinal
  intro H hf
  obtain ⟨i, hi, hw⟩ := hcover H hf
  have hh := hits_of_mem (appendFinalQuery tree point) H (support i) (point (tree.run H).1)
    (appendFinalQuery_mem tree point H) hi
  have hn (j : I) : 0 ≤ (if hits (appendFinalQuery tree point) H (support j) then weight j H else 0) := by
    split_ifs
    · exact hweight j H
    · exact le_rfl
  exact hw.trans (by simpa [hh] using single_le_sum (fun j _ => hn j) (mem_univ i))

end Bcs.TotalOracle.Footprint
