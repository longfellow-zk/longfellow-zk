import Survival.History
import TranscriptV2.Composition

/-! Apply the existing all-orders joint-response charging theorem to the
stopped tree. The weights remain tied to the ORIGINAL tree/cut. This is an
application of the existing theorem, not a conditional backend assumption.
-/
noncomputable section
namespace Survival.StoppedCharges
open Finset Merkle.RandomOracle Bcs.FiniteProbability TranscriptV2
open scoped Classical

variable {P D C Parent Response Out S : Type}
variable [Fintype P] [DecidableEq P] [Fintype D] [Nonempty D]
variable [Fintype C] [Nonempty C] [Fintype Parent] [Fintype Response]

omit [Fintype P] [DecidableEq P] [Fintype Parent] in
theorem pair_budget_nonneg (original : Composition.LocalCharges P D C Parent Response) (parent : Parent) :
    0 ≤ original.pairBudget parent := by
  let answer : D × C := Classical.choice (inferInstance : Nonempty (D × C))
  have nonnegative : 0 ≤ ∑ response, ∑ a, ∑ b, original.pair parent response (fun _ => answer) a b :=
    sum_nonneg (fun response _ => sum_nonneg (fun a _ => sum_nonneg (fun b _ =>
      original.pair_nonneg parent response (fun _ => answer) a b)))
  have bound := original.pair_mean parent (fun _ => answer)
  have positive : (0 : ℚ) < (Fintype.card (D × C) : ℚ)^2 := by positivity
  nlinarith

omit [Fintype P] in
theorem singleBudget_le_budget (original : Composition.LocalCharges P D C Parent Response) (point : P) :
    original.singleBudget point ≤ original.budget point := by
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro parent _
  split_ifs
  · exact pair_budget_nonneg original parent
  · exact le_rfl

/-- Discard transparent single-answer charges; preserve the original pair
weights, original source cut, and their existing independence/mean laws. -/
def restrict (original : Composition.LocalCharges P D C Parent Response) (marked : P → Bool) :
    Composition.LocalCharges P D C Parent Response where
  parent := original.parent
  child := original.child
  distinct := original.distinct
  single p H a := if marked p then original.single p H a else 0
  pair := original.pair
  single_nonneg p H a := by split_ifs; exact original.single_nonneg p H a; exact le_rfl
  pair_nonneg := original.pair_nonneg
  single_off p H H' agree a := by simp only [original.single_off p H H' agree a]
  pair_off := original.pair_off
  singleBudget p := if marked p then original.singleBudget p else 0
  pairBudget := original.pairBudget
  single_mean p H := by
    by_cases hm : marked p = true
    · simpa only [hm, if_true] using original.single_mean p H
    · simp [hm]
  pair_mean := original.pair_mean

omit [Fintype P] [Nonempty D] [Nonempty C] in
theorem restrict_budget (original : Composition.LocalCharges P D C Parent Response)
    (marked : P → Bool) (parents : ∀ parent, marked (original.parent parent) = true) (point : P) :
    (restrict original marked).budget point = if marked point then original.budget point else 0 := by
  by_cases hm : marked point = true
  · simp only [Composition.LocalCharges.budget, restrict, hm, if_true]
  · have absent (parent : Parent) : original.parent parent ≠ point := by
      intro same
      exact hm (same ▸ parents parent)
    simp only [Composition.LocalCharges.budget, restrict, hm, if_false, absent, sum_const_zero, add_zero]

omit [Fintype P] [Nonempty D] [Nonempty C] [DecidableEq P] [Fintype Parent] in
theorem covers_restrict (original : Composition.LocalCharges P D C Parent Response)
    (marked : P → Bool) {rounds : ℕ} (path : ℕ → P) (H : P → D × C)
    (cover : original.Covers (rounds := rounds) path H)
    (transparent : ∀ i < rounds, marked (path i) = false → original.single (path i) H (H (path i)) < 1) :
    (restrict original marked).Covers (rounds := rounds) path H := by
  rcases cover with ⟨i,within,charged⟩ | pair
  · have hm : marked (path i) = true := by
      cases flag : marked (path i) with
      | true => rfl
      | false => exact False.elim (not_le_of_gt (transparent i within flag) charged)
    exact Or.inl ⟨i,within,by simpa only [restrict, hm, if_true] using charged⟩
  · exact Or.inr pair

omit [Fintype P] [Fintype D] [Nonempty D] [Fintype C] [Nonempty C] in
theorem marked_card_le (safe : S × P → D × C → Prop) (marked : P → Bool)
    (step : S → P → D × C → S) {fuel : ℕ} (state : S) (tree : Tree P (D × C) Out fuel)
    (H : P → D × C) :
    ((seen (History.audit safe marked step state tree) H).filter fun p => marked p = true).card ≤
      ((History.audit safe marked step state tree).run H).1.2 := by
  let trace := ((History.audit safe marked step state tree).run H).2
  have sets : (seen (History.audit safe marked step state tree) H).filter (fun p => marked p = true) =
      ((trace.filter fun qa => marked qa.1).map Prod.fst).toFinset := by
    ext p
    simp only [seen, Bcs.TotalOracle.queried, mem_filter, List.mem_toFinset, List.mem_map,
      List.mem_filter, trace]
    constructor
    · rintro ⟨⟨qa,member,rfl⟩,hm⟩
      exact ⟨qa,⟨member,hm⟩,rfl⟩
    · rintro ⟨qa,⟨member,hm⟩,rfl⟩
      exact ⟨⟨qa,member,rfl⟩,hm⟩
  rw [sets, History.audit_count]
  exact (List.toFinset_card_le _).trans_eq (List.length_map _)

omit [Fintype P] [Fintype D] [Nonempty D] [Fintype C] [Nonempty C] in
theorem slots_le (safe : S × P → D × C → Prop) (marked : P → Bool) (step : S → P → D × C → S)
    (allowance : ℚ) (positive : 0 ≤ allowance)
    {fuel : ℕ} (state : S) (tree : Tree P (D × C) Out fuel) (H : P → D × C) :
    (∑ p ∈ seen (History.audit safe marked step state tree) H, if marked p then allowance else 0) ≤
      allowance * (((History.audit safe marked step state tree).run H).1.2 : ℚ) := by
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (marked_card_le safe marked step state tree H)) positive

theorem mean_le (original : Composition.LocalCharges P D C Parent Response)
    (safe : S × P → D × C → Prop) (marked : P → Bool) (step : S → P → D × C → S)
    (allowance : ℚ) (positive : 0 ≤ allowance)
    (budget : ∀ p, (restrict original marked).budget p ≤ if marked p then allowance else 0)
    {fuel : ℕ} (state : S) (tree : Tree P (D × C) Out fuel) :
    (∑ H, (restrict original marked).charge (History.audit safe marked step state tree) H) /
        Fintype.card (P → D × C) ≤
      allowance * ((∑ H : P → D × C, (((History.audit safe marked step state tree).run H).1.2 : ℚ)) /
        Fintype.card (P → D × C)) := by
  have average := (restrict original marked).charge_mean
    (History.audit safe marked step state tree) (fun p => if marked p then allowance else 0) budget
  have total := average.trans (sum_le_sum (fun H _ => slots_le safe marked step allowance positive state tree H))
  have divided := div_le_div_of_nonneg_right total
    (show (0 : ℚ) ≤ Fintype.card (P → D × C) by positivity)
  simpa only [← mul_sum, mul_div_assoc] using divided

/-- Backend and hash charges use disjoint opaque slots. Combining their
means before counting slots prevents charging the opaque allowance twice. -/
theorem combined_mean_le (original : Composition.LocalCharges P D C Parent Response)
    (safe : S × P → D × C → Prop) (marked auxiliary : P → Bool) (step : S → P → D × C → S)
    (auxiliary_marked : ∀ point, auxiliary point = true → marked point = true)
    (allowance : ℚ) (positive : 0 ≤ allowance)
    (budget : ∀ p, (restrict original marked).budget p ≤
      if marked p && !auxiliary p then allowance else 0)
    {fuel : ℕ} (state : S) (tree : Tree P (D × C) Out fuel)
    (hashCost : (P → D × C) → ℚ)
    (hash_mean : (∑ H, hashCost H) ≤ ∑ H : P → D × C,
      ∑ p ∈ seen (History.audit safe marked step state tree) H, if auxiliary p then allowance else 0) :
    (∑ H, ((restrict original marked).charge (History.audit safe marked step state tree) H + hashCost H)) /
        Fintype.card (P → D × C) ≤
      allowance * ((∑ H : P → D × C, (((History.audit safe marked step state tree).run H).1.2 : ℚ)) /
        Fintype.card (P → D × C)) := by
  have backend := (restrict original marked).charge_mean (History.audit safe marked step state tree)
    (fun p => if marked p && !auxiliary p then allowance else 0) budget
  have together := add_le_add backend hash_mean
  rw [← sum_add_distrib, ← sum_add_distrib] at together
  have per_point (p : P) :
      (if marked p && !auxiliary p then allowance else 0) +
        (if auxiliary p then allowance else 0) = if marked p then allowance else 0 := by
    by_cases ha : auxiliary p = true
    · simp only [ha, auxiliary_marked p ha, Bool.not_true, Bool.and_false,
        Bool.false_eq_true, if_false, if_true, zero_add]
    · have noAux : auxiliary p = false := Bool.eq_false_iff.mpr ha
      simp only [noAux, Bool.not_false, Bool.and_true, Bool.false_eq_true, if_false, add_zero]
  have slots (H : P → D × C) :
      (∑ p ∈ seen (History.audit safe marked step state tree) H,
        if marked p && !auxiliary p then allowance else 0) +
      (∑ p ∈ seen (History.audit safe marked step state tree) H,
        if auxiliary p then allowance else 0) ≤
      allowance * (((History.audit safe marked step state tree).run H).1.2 : ℚ) := by
    rw [← sum_add_distrib]
    simp_rw [per_point]
    exact slots_le safe marked step allowance positive state tree H
  have total := together.trans (sum_le_sum (fun H _ => slots H))
  have divided := div_le_div_of_nonneg_right total
    (show (0 : ℚ) ≤ Fintype.card (P → D × C) by positivity)
  simpa only [← mul_sum, mul_div_assoc] using divided

end Survival.StoppedCharges
