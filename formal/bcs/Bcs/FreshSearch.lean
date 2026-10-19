import Bcs.FootprintCharging

/-!
# Fresh adaptive trees: total-oracle and independent-sample expectations

`FreshFrom seen` certifies that every syntactic continuation avoids every
previous query. It therefore allows each newly read coordinate to be
averaged as a fresh independent answer, even for adaptively chosen inputs.
-/
namespace Bcs.TotalOracle.FreshSearch

open Finset Merkle.RandomOracle Footprint
open scoped Classical

variable {Q C Out : Type} [DecidableEq Q]

/-- Every branch avoids the queries already made, and adds its next query
to that set before entering its selected continuation. -/
def FreshFrom (seen : Finset Q) : {N : ℕ} → Tree Q C Out N → Prop
  | _, .done _ => True
  | _, .query q next => q ∉ seen ∧ ∀ c, FreshFrom (insert q seen) (next c)

@[simp] theorem FreshFrom_weaken {N : ℕ} (tree : Tree Q C Out N) (seen : Finset Q) :
    FreshFrom seen tree.weaken ↔ FreshFrom seen tree := by
  induction tree generalizing seen with
  | done out => rfl
  | query q next ih => simp [Tree.weaken, FreshFrom, ih]

@[simp] theorem FreshFrom_weakenAdd {N : ℕ} (tree : Tree Q C Out N)
    (seen : Finset Q) (extra : ℕ) :
    FreshFrom seen (tree.weakenAdd extra) ↔ FreshFrom seen tree := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [Tree.weakenAdd, ih]

theorem avoids_seen {N : ℕ} (tree : Tree Q C Out N) (seen : Finset Q)
    (hfresh : FreshFrom seen tree) (H : Q → C) :
    ∀ q ∈ seen, q ∉ queried tree H := by
  induction tree generalizing seen with
  | done out => simp
  | query q next ih =>
      intro x hx
      rw [queried_query, List.mem_cons, not_or]
      constructor
      · intro he
        exact hfresh.1 (he ▸ hx)
      · exact ih (H q) (insert q seen) (hfresh.2 (H q)) x (mem_insert_of_mem hx)

variable [Fintype C] [Nonempty C]

/-- The expectation obtained by drawing a new independent answer at every
query. Without freshness it need not equal total-random-oracle execution. -/
noncomputable def iidExpectation (payoff : Out → ℚ) :
    {N : ℕ} → Tree Q C Out N → ℚ
  | _, .done out => payoff out
  | _, .query _ next => average (fun c => iidExpectation payoff (next c))

omit [DecidableEq Q] [Nonempty C] in
@[simp] theorem iidExpectation_weaken {N : ℕ} (tree : Tree Q C Out N)
    (payoff : Out → ℚ) : iidExpectation payoff tree.weaken = iidExpectation payoff tree := by
  induction tree with
  | done out => rfl
  | query q next ih => simp [Tree.weaken, iidExpectation, ih]

omit [DecidableEq Q] [Nonempty C] in
@[simp] theorem iidExpectation_weakenAdd {N : ℕ} (tree : Tree Q C Out N)
    (payoff : Out → ℚ) (extra : ℕ) :
    iidExpectation payoff (tree.weakenAdd extra) = iidExpectation payoff tree := by
  induction extra with
  | zero => rfl
  | succ extra ih => simp [Tree.weakenAdd, ih]

variable [Fintype Q]

private theorem average_off_coordinate (q : Q)
    (wt : (Q → C) → C → ℚ)
    (hoff : ∀ H H', AgreeOff q H H' → ∀ c, wt H c = wt H' c) :
    average (fun H => wt H (H q)) = average (fun c => average (fun H => wt H c)) := by
  have h := sum_coord_mul_rat q wt hoff
  have hc : (Fintype.card C : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hh : (Fintype.card (Q → C) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold average
  simp only [← sum_div]
  rw [sum_comm]
  apply (div_eq_div_iff hh hc).mpr
  rw [div_mul_cancel₀ _ hh]
  exact h

/-- Exact eager/independent sampling equivalence for a structurally fresh
adaptive tree, with an arbitrary rational output payoff. -/
theorem totalOracle_eq_iid {N : ℕ} (tree : Tree Q C Out N) (seen : Finset Q)
    (hfresh : FreshFrom seen tree) (payoff : Out → ℚ) :
    average (fun H : Q → C => payoff (tree.run H).1) = iidExpectation payoff tree := by
  induction tree generalizing seen with
  | done out => simp [iidExpectation]
  | query q next ih =>
      change average (fun H => payoff ((next (H q)).run H).1) =
        average (fun c => iidExpectation payoff (next c))
      calc
        _ = average (fun c => average (fun H : Q → C => payoff ((next c).run H).1)) := by
          apply average_off_coordinate q (fun H c => payoff ((next c).run H).1)
          intro H H' hagree c
          have hq := avoids_seen (next c) (insert q seen) (hfresh.2 c) H q (mem_insert_self _ _)
          exact congrArg (fun out => payoff out.1)
            (run_eq_of_not_mem (next c) q hagree hq).symm
        _ = _ := by
          apply congrArg average
          funext c
          exact ih c (insert q seen) (hfresh.2 c)

end Bcs.TotalOracle.FreshSearch
