import Bcs.TerminalCharges

set_option maxHeartbeats 1500000

/-! Context-dependent footprint prices and a verifier replay. Prices can
read the complementary oracle. Their incidence is checked jointly on each
oracle, so correlated budgets need not be replaced by separate maxima. -/
namespace Bcs.TotalOracle.Footprint
open Finset Merkle.RandomOracle Bcs.AffineBlock
open scoped Classical
variable {Q C Out I : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
  [Fintype I]

omit [Fintype Q] [Fintype C] [Nonempty C] [Fintype I] in
theorem hits_bind {N R : ℕ} (tree : Tree Q C Out N)
    (replay : Out → Tree Q C Unit R) (H : Q → C) (s : Finset Q) :
    hits (tree.bind replay) H s = (hits tree H s || hits (replay (tree.run H).1) H s) := by
  induction tree with
  | done out => simp [Tree.bind, hits, hits_weakenAdd]
  | query q next ih =>
    by_cases hq : q ∈ s
    · simp [Tree.bind, hits, hq]
    · simpa only [Tree.bind, hits, if_neg hq, Tree.run_query] using ih (H q)

omit [Fintype Q] [Fintype C] [Nonempty C] in
/-- Pathwise accounting before averaging. The replay has an independent
completion budget; arbitrary repeated prover queries are allowed. -/
theorem activated_replay_budget_le {N R : ℕ} (tree : Tree Q C Out N)
    (replay : Out → Tree Q C Unit R) (support : I → Finset Q)
    (budget : I → ℚ) (domain : Finset Q) (epsilon kappa : ℚ)
    (hn : ∀ i, 0 ≤ budget i)
    (hquery : ∀ q, (∑ i, if q ∈ support i then budget i else 0) ≤
      if q ∈ domain then kappa else 0)
    (hfinal : ∀ out H, (∑ i, if hits (replay out) H (support i) then budget i else 0) ≤ epsilon)
    (H : Q → C) :
    (∑ i, if hits (tree.bind replay) H (support i) then budget i else 0) ≤
      epsilon + queryCost domain tree H*kappa := by
  induction tree with
  | done out => simpa [Tree.bind, hits_weakenAdd, queryCost] using hfinal out H
  | query q next ih =>
    have hs :
        (∑ i, if hits ((Tree.query q next).bind replay) H (support i) then budget i else 0) ≤
        (∑ i, if q ∈ support i then budget i else 0) +
          ∑ i, if hits ((next (H q)).bind replay) H (support i) then budget i else 0 := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro i _
      by_cases hi : q ∈ support i
      · simp only [Tree.bind, hits, if_pos hi, ↓reduceIte]
        split_ifs <;> linarith [hn i]
      · simp only [Tree.bind, hits, if_neg hi, zero_add]
        exact le_rfl
    refine hs.trans ((add_le_add (hquery q) (ih (H q))).trans ?_)
    by_cases hq : q ∈ domain
    · simp only [queryCost,hq,if_true]; linarith
    · simp only [queryCost,hq,if_false,zero_add]; exact le_rfl

end Bcs.TotalOracle.Footprint

namespace Bcs.AffineBlock
open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

/-- A block compiler with contextual, jointly bounded prices and explicit
verifier completion. This is still the same two-parameter ABS interface. -/
theorem oracle_sound_of_contextual_footprints
    {Q C Out I : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] [Fintype I]
    {R : ℕ} (domain : Finset Q) (replay : Out → Tree Q C Unit R)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ) (rate : Rate)
    (hn : ∀ i H, 0 ≤ weight i H) (hb : ∀ i off, 0 ≤ budget i off)
    (hl : ∀ i off,
      average (fun on => weight i ((split (support i)).symm (on,off))) ≤ budget i off)
    (hq : ∀ (H : Q → C) q, (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤
      if q ∈ domain then rate.slope else 0)
    (hf : ∀ (H : Q → C) out (H' : Q → C),
      (∑ i, if hits (replay out) H' (support i) then budget i (fun z => H z.1) else 0) ≤ rate.intercept)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ out H, failure out H →
      1 ≤ ∑ i, if hits (replay out) H (support i) then weight i H else 0) :
    OracleSound domain failure rate := by
  intro N tree
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  have he := event_le_expected_budget (tree.bind replay) support weight budget
    (fun H => failure (tree.run H).1 H) hn hl (by
      intro H hf
      refine (hpay _ H hf).trans (sum_le_sum (fun i _ => ?_))
      rw [hits_bind]
      cases hits tree H (support i) <;> cases hits (replay (tree.run H).1) H (support i) <;>
        simp [hn])
  refine he.trans ?_
  calc
    _ ≤ average (fun H => rate.intercept + queryCost domain tree H*rate.slope) := by
      apply average_mono
      intro H
      exact activated_replay_budget_le tree replay support
        (fun i => budget i (fun z => H z.1)) domain rate.intercept rate.slope
        (fun i => hb i _) (hq H) (hf H) H
    _ = rate.intercept + rate.slope*average (queryCost domain tree) := by
      simp only [average_add, average_const]
      rw [show (fun H => queryCost domain tree H*rate.slope) =
        (fun H => rate.slope*queryCost domain tree H) by funext H; ring, average_mul]

end Bcs.AffineBlock

namespace Bcs.TotalOracle.Footprint
open Finset Merkle.RandomOracle Bcs.AffineBlock
open scoped Classical
variable {Q C Out I : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] [Fintype I]

noncomputable def footprintCharge {N : ℕ} (tree : Tree Q C Out N)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ) (H : Q → C) : ℚ :=
  ∑ i, if hits tree H (support i) then weight i H else 0

theorem footprintCharge_average_le {N : ℕ} (tree : Tree Q C Out N)
    (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ) (domain : Finset Q) (slope : ℚ)
    (hb : ∀ i off, 0 ≤ budget i off)
    (hl : ∀ i off, average (fun on => weight i ((split (support i)).symm (on,off))) ≤ budget i off)
    (hq : ∀ (H : Q → C) q,
      (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤ if q ∈ domain then slope else 0) :
    average (footprintCharge tree support weight) ≤ slope*average (queryCost domain tree) := by
  have hp (H : Q → C) :
      (∑ i, if hits tree H (support i) then budget i (fun z => H z.1) else 0) ≤ queryCost domain tree H*slope := by
    have h := activated_replay_budget_le tree (fun _ => (Tree.done () : Tree Q C Unit 0)) support
      (fun i => budget i (fun z => H z.1)) domain 0 slope (fun i => hb i _) (hq H)
      (by intros; simp [hits]) H
    simpa only [hits_bind,hits,Bool.or_false,zero_add] using h
  calc
    _ ≤ average (fun H => ∑ i, if hits tree H (support i) then budget i (fun z => H z.1) else 0) := by
      unfold footprintCharge
      rw [average_sum,average_sum]
      exact sum_le_sum (fun i _ => activated_average_le tree _ _ _ (hl i))
    _ ≤ average (fun H => queryCost domain tree H*slope) := average_mono hp
    _ = _ := by
      rw [show (fun H => queryCost domain tree H*slope) = (fun H => slope*queryCost domain tree H)
        by funext H; ring, average_mul]

end Bcs.TotalOracle.Footprint

namespace Bcs.AffineBlock
open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

/-- Whole-footprint prover charging can be combined with a joint
completion of only the unread selected verifier coordinates. -/
theorem oracle_sound_of_contextual_footprint_completion
    {Q C Out I : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C] [Fintype I]
    (domain : Finset Q) (support : I → Finset Q) (weight : I → (Q → C) → ℚ)
    (budget : ∀ i, (Outside (support i) → C) → ℚ) (rate : Rate)
    (hn : ∀ i H, 0 ≤ weight i H) (hb : ∀ i off, 0 ≤ budget i off)
    (hl : ∀ i off, average (fun on => weight i ((split (support i)).symm (on,off))) ≤ budget i off)
    (hq : ∀ (H : Q → C) q,
      (∑ i, if q ∈ support i then budget i (fun z => H z.1) else 0) ≤ if q ∈ domain then rate.slope else 0)
    (completion : {N : ℕ} → Tree Q C Out N → (Q → C) → ℚ)
    (hcn : ∀ N (tree : Tree Q C Out N) H, 0 ≤ completion tree H)
    (hcm : ∀ N (tree : Tree Q C Out N), average (completion tree) ≤ rate.intercept)
    (failure : Out → (Q → C) → Prop)
    (hpay : ∀ N (tree : Tree Q C Out N) H, failure (tree.run H).1 H →
      1 ≤ footprintCharge tree support weight H+completion tree H) :
    OracleSound domain failure rate := by
  intro N tree
  refine ⟨queryCost_nonneg domain tree, ?_⟩
  rw [density_eq_average]
  have hp (H : Q → C) : (if failure (tree.run H).1 H then (1 : ℚ) else 0) ≤
      footprintCharge tree support weight H+completion tree H := by
    by_cases hf : failure (tree.run H).1 H
    · simpa only [if_pos hf] using hpay N tree H hf
    · simp only [if_neg hf]
      exact add_nonneg (sum_nonneg fun i _ => by split_ifs; exact hn i H; rfl) (hcn N tree H)
  refine (average_mono hp).trans ?_
  rw [average_add]
  have hs := footprintCharge_average_le tree support weight budget domain rate.slope hb hl hq
  linarith [hcm N tree]

end Bcs.AffineBlock
