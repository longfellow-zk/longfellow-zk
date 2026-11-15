import SumcheckV2.DotProduct

/-!
# Single-hand layer reduction

`K l r` is the effective quadratic coefficient after binding output weights and
replacing assertion coefficients. Both tensor bindings must use this same `K`.
The prover reduces `dot q_l W`, and the verifier re-expresses the second final
claim using the public transpose binding `q_r`.
-/

namespace SumcheckV2

open Classical

variable {F : Type} [Field F]

def bindRight {ι : Type} [Fintype ι] (K : ι → ι → F) (w : ι → F) : ι → F :=
  fun l => ∑ r, K l r * w r

def bindLeft {ι : Type} [Fintype ι] (K : ι → ι → F) (m : ι → F) : ι → F :=
  fun r => ∑ l, K l r * m l

/-- The two tensor bindings compute the same scalar. -/
theorem tensor_rebinding {ι : Type} [Fintype ι] (K : ι → ι → F) (m w : ι → F) :
    dot m (bindRight K w) = dot (bindLeft K m) w := by
  simp only [dot, bindRight, bindLeft, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro l _
  ring

def nextWeights {ι : Type} [Fintype ι] (K : ι → ι → F) (m : ι → F)
    (alpha : F) : ι → F := fun i => m i + alpha * bindLeft K m i

theorem nextWeights_correct {ι : Type} [Fintype ι]
    (K : ι → ι → F) (m w : ι → F) (alpha : F) :
    dot (nextWeights K m alpha) w = dot m w + alpha * dot m (bindRight K w) := by
  rw [tensor_rebinding]
  simp only [dot, nextWeights, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- A wrong pair of claims happens to combine to the true next claim. -/
def BadCombineEvent (A B a b alpha : F) : Prop :=
  (a ≠ A ∨ b ≠ B) ∧ a + alpha * b = A + alpha * B

/-- Final claims are fixed before `alpha`: at most one value repairs a wrong pair. -/
theorem bad_combine_roots [Fintype F] [DecidableEq F] (A B a b : F) :
    (Finset.univ.filter fun alpha => BadCombineEvent A B a b alpha).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hwrong, hx⟩ := (Finset.mem_filter.mp hx).2
  have hy := (Finset.mem_filter.mp hy).2.2
  have hb : b - B ≠ 0 := by
    intro h
    have hB : b = B := sub_eq_zero.mp h
    have hA : a = A := by rw [hB] at hx; exact add_right_cancel hx
    exact hwrong.elim (fun h => h hA) (fun h => h hB)
  have hprod : (x - y) * (b - B) = 0 := by linear_combination hx - hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hb)

/-- Honest final claims pass the terminal product check and combine correctly. -/
theorem layer_completeness {n : ℕ} (K : Cube n → Cube n → F) (w : Cube n → F)
    (u : Fin n → F) (alpha : F) :
    verify_multi_round (dot (bindRight K w) w)
        (honestMessages (bindRight K w) w u) (List.ofFn u) =
      some (evaluate w u * evaluate (bindRight K w) u) ∧
    evaluate w u + alpha * evaluate (bindRight K w) u =
      dot (nextWeights K (monomialWeights u) alpha) w := by
  constructor
  · simpa [mul_comm] using honest_completeness (bindRight K w) w u
  · rw [nextWeights_correct, evaluate_eq_dot, evaluate_eq_dot]

/-- If a false layer claim reaches a true next claim, a round or the combination was bad.
The product check is essential: it connects the sumcheck's final state to `a * b`. -/
theorem layer_reduction {n : ℕ} (K : Cube n → Cube n → F) (w : Cube n → F)
    (u : Fin n → F) (claim a b alpha : F) (messages : List (RoundPoly F))
    (hfalse : claim ≠ dot (bindRight K w) w)
    (hterminal : verify_multi_round claim messages (List.ofFn u) = some (a * b))
    (hnext : a + alpha * b = dot (nextWeights K (monomialWeights u) alpha) w) :
    multi_round_bad_event claim (truePolys (bindRight K w) w u) messages (List.ofFn u) ∨
      BadCombineEvent (evaluate w u) (evaluate (bindRight K w) u) a b alpha := by
  by_cases hpair : a = evaluate w u ∧ b = evaluate (bindRight K w) u
  · left
    apply dot_product_reduction (bindRight K w) w u claim messages hfalse
    simpa [hpair.1, hpair.2, mul_comm] using hterminal
  · right
    constructor
    · tauto
    · simpa only [nextWeights_correct, ← evaluate_eq_dot] using hnext

end SumcheckV2
