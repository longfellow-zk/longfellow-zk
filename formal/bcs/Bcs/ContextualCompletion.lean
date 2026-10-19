import Bcs.PairCompletion

set_option maxHeartbeats 1500000

/-! Joint completion with root-cut contexts. The bad event may depend on
the outside oracle; the fresh-pair mean is proved on the actual held-out pair. -/
namespace Bcs.AffineBlock
open Finset TotalOracle TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical
variable {Q C Out : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
  [Fintype Out] [DecidableEq Out]

noncomputable def contextualPairCompletion (x y : Out → Q)
    (weight : Q → (Q → C) → C → ℚ) (bad : Out → (Q → C) → Prop)
    (out : Out) (seen : Finset Q) (H : Q → C) : ℚ :=
  if x out ∈ seen then
    if y out ∈ seen then 0 else weight (y out) H (H (y out))
  else if y out ∈ seen then weight (x out) H (H (x out))
  else if bad out H then 1 else 0

/-- Local point charges pay prover exposure. At termination, complete
just the unread part of the selected pair. If neither point was read,
use their joint event mean instead of adding two separate slot budgets. -/
theorem oracle_sound_of_contextual_pair_completion
    (domain : Finset Q) (x y : Out → Q) (hxy : ∀ out, x out ≠ y out)
    (weight : Q → (Q → C) → C → ℚ)
    (hoff : ∀ q H H', AgreeOff q H H' → ∀ c, weight q H c = weight q H' c)
    (hn : ∀ q H c, 0 ≤ weight q H c)
    (rate : Rate) (hsi : rate.slope ≤ rate.intercept)
    (hlocal : ∀ q H, ∑ c, weight q H c ≤
      if q ∈ domain then Fintype.card C * rate.slope else 0)
    (bad : Out → (Q → C) → Prop)
    (hjoint : ∀ out (off : Outside ({x out,y out} : Finset Q) → C),
      average (fun on => if bad out ((split {x out,y out}).symm (on,off))
        then (1 : ℚ) else 0) ≤ rate.intercept)
    (hpay : ∀ out H, bad out H →
      1 ≤ weight (x out) H (H (x out)) + weight (y out) H (H (y out))) :
    OracleSound domain (fun out H => bad out H) rate := by
  classical
  let completion {N} (tree : Tree Q C Out N) (H : Q → C) :=
    contextualPairCompletion x y weight bad (tree.run H).1 (queried tree H).toFinset H
  have hpoint (q : Q) (H : Q → C) : average (weight q H) ≤ rate.intercept := by
    have hc : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hc).mpr
    have he := hlocal q H
    have hs := mul_le_mul_of_nonneg_left hsi hc.le
    split_ifs at he
    · linarith
    · exact he.trans (mul_nonneg rate.intercept_nonneg hc.le)
  apply oracle_sound_of_completion domain weight hoff hn rate hlocal completion ?_ ?_ _ ?_
  · intro N tree
    apply trace_completion_average_le tree (fun out seen => {x out, y out} \ seen)
      (contextualPairCompletion x y weight bad) rate.intercept
    · intros; exact disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp h).2 h')
    · intro out seen
      by_cases hx : x out ∈ seen <;> by_cases hy : y out ∈ seen
      · intro off
        simp only [contextualPairCompletion, hx, hy, ↓reduceIte, average_const]
        exact rate.intercept_nonneg
      · have hs : ({x out, y out} : Finset Q) \ seen = {y out} := by ext q; simp; aesop
        rw [hs]
        intro off
        simpa only [contextualPairCompletion, hx, hy, ↓reduceIte] using
          singleton_completion_mean (y out) (weight (y out)) (hoff (y out))
            rate.intercept (hpoint (y out)) off
      · have hs : ({x out, y out} : Finset Q) \ seen = {x out} := by ext q; simp; aesop
        rw [hs]
        intro off
        simpa only [contextualPairCompletion, hx, hy, ↓reduceIte] using
          singleton_completion_mean (x out) (weight (x out)) (hoff (x out))
            rate.intercept (hpoint (x out)) off
      · have hs : ({x out, y out} : Finset Q) \ seen = {x out, y out} := by ext q; simp; aesop
        rw [hs]
        intro off
        simpa only [contextualPairCompletion, hx, hy, ↓reduceIte] using hjoint out off

  · intro N tree H
    dsimp [completion, contextualPairCompletion]
    split_ifs <;> first | exact hn _ _ _ | norm_num
  · intro N tree H hb
    let out := (tree.run H).1
    let seen := (queried tree H).toFinset
    have hnon (q : Q) : 0 ≤ if q ∈ queried tree H then weight q H (H q) else 0 := by
      split_ifs; exact hn _ _ _; rfl
    have hroot (hx : x out ∈ seen) : weight (x out) H (H (x out)) ≤ proverCharge tree weight H := by
      simpa only [proverCharge, List.mem_toFinset.mp hx, ↓reduceIte] using
        single_le_sum (fun q (_ : q ∈ univ) => hnon q) (mem_univ (x out))
    have hchild (hy : y out ∈ seen) : weight (y out) H (H (y out)) ≤ proverCharge tree weight H := by
      simpa only [proverCharge, List.mem_toFinset.mp hy, ↓reduceIte] using
        single_le_sum (fun q (_ : q ∈ univ) => hnon q) (mem_univ (y out))
    have htotal := hpay out H hb
    change 1 ≤ proverCharge tree weight H + contextualPairCompletion x y weight bad out seen H
    by_cases hx : x out ∈ seen <;> by_cases hy : y out ∈ seen
    · have hp : weight (x out) H (H (x out)) + weight (y out) H (H (y out)) ≤
          proverCharge tree weight H := by
        have hs : ({x out, y out} : Finset Q) ⊆ univ := subset_univ _
        have he := sum_le_sum_of_subset_of_nonneg hs (fun q _ _ => hnon q)
        simpa [sum_pair (hxy out), proverCharge, List.mem_toFinset.mp hx,
          List.mem_toFinset.mp hy] using he
      simpa only [contextualPairCompletion, hx, hy, ↓reduceIte, add_zero] using htotal.trans hp
    · simp only [contextualPairCompletion, hx, hy, ↓reduceIte]
      linarith [hroot hx]
    · simp only [contextualPairCompletion, hx, hy, ↓reduceIte]
      linarith [hchild hy]
    · have hp : 0 ≤ proverCharge tree weight H := sum_nonneg fun q _ => hnon q
      have hb' : bad out H := hb
      simp only [contextualPairCompletion, hx, hy, hb', ↓reduceIte]
      linarith

end Bcs.AffineBlock
