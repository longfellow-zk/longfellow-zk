import Mathlib.GroupTheory.OrderOfElement
import ECDSA.Pratt
import GF128.Field

/-!
# `α` has order `2^128 − 1`

`GF128/Field.lean` transferred the two halves of the Lucas certificate into `F`:
`α^N = 1` and `α^(N/q) ≠ 1` for each `q` in `NFactors`. Turning those into a statement about
`orderOf` needs one more thing — that `NFactors` really is *every* prime dividing `N`, which is
`NFactors_prod` together with primality of each entry.

Eight of the nine are within `norm_num`'s reach. `67280421310721` is not — `norm_num` runs the
kernel out of time on it — so it gets an explicit Pratt certificate in the style of
`ECDSA/Pratt.lean`, whose machinery this file borrows. That is the only reason this module is
separate from `Field.lean`: it pays for Mathlib's group theory and for `ECDSA.PowMod`, and
nothing below it should have to.
-/

set_option maxRecDepth 40000
set_option exponentiation.threshold 300

namespace GF128

open ECDSA

/-- `2^64 + 1 = 274177 · 67280421310721`; this is the large half.
    `n − 1 = 2^8 · 5 · 47 · 373 · 2998279`, with `3` a primitive root. -/
theorem prime_67280421310721 : Nat.Prime 67280421310721 := by
  refine lucas_primality 67280421310721 ((3 : ℕ) : ZMod 67280421310721) ?_ ?_
  · exact cast_pow_eq_one (fuel := 300) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 67280421310721 - 1
        = ([2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 373, 2998279] : List ℕ).prod := by norm_num
    have hmem := mem_of_prime_dvd_prod
      (by intro q hq; fin_cases hq <;> norm_num) hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact cast_pow_ne_one (fuel := 300) (by norm_num) (by decide) (by decide)

/-- Every entry of `NFactors` is prime. -/
theorem NFactors_prime : ∀ q ∈ NFactors, Nat.Prime q := by
  intro q hq
  simp only [NFactors, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact prime_67280421310721

variable {F : Type*} [CommRing F] [CharP F 2]

/-- Every prime dividing `N` is one of `NFactors`. -/
theorem mem_NFactors_of_prime_dvd {q : Nat} (hq : Nat.Prime q) (hd : q ∣ N) : q ∈ NFactors := by
  have hprod : N = NFactors.prod := by
    have h := NFactors_prod
    simpa [NFactors, List.prod] using h.symm
  exact mem_of_prime_dvd_prod NFactors_prime hq (hprod ▸ hd)

/-- **`α` is primitive: its multiplicative order is `2^128 − 1`.** -/
theorem orderOf_alpha (α : F) (h : IsGen α) : orderOf α = N :=
  orderOf_eq_of_pow_and_pow_div_prime (by decide) (alpha_pow_N_eq_one α h)
    (fun q hq hd => alpha_pow_div_ne_one α h (mem_NFactors_of_prime_dvd hq hd))

/-- What the wrapping sum actually consumes: distinct exponents below `N` give distinct powers.
    The adder needs this only up to `2^32 · 7`, so the slack is about `2^93`. -/
theorem alpha_pow_ne_one (α : F) (h : IsGen α) {k : Nat} (hk : 0 < k) (hlt : k < N) :
    α ^ k ≠ 1 := by
  intro hc
  have hdvd : orderOf α ∣ k := orderOf_dvd_of_pow_eq_one hc
  rw [orderOf_alpha α h] at hdvd
  exact absurd (Nat.le_of_dvd hk hdvd) (by omega)

theorem alpha_ne_zero [Nontrivial F] (α : F) (h : IsGen α) : α ≠ 0 := by
  intro h0
  have hN := alpha_pow_N_eq_one α h
  rw [h0, zero_pow (by decide : N ≠ 0)] at hN
  exact zero_ne_one hN

private theorem pow_sub_eq_one [IsDomain F] (α : F) (hne : α ≠ 0) {m n : Nat} (hle : n ≤ m)
    (heq : α ^ m = α ^ n) : α ^ (m - n) = 1 := by
  have hsplit : α ^ m = α ^ n * α ^ (m - n) := by
    rw [← pow_add]; congr 1; omega
  refine mul_left_cancel₀ (pow_ne_zero n hne) ?_
  rw [mul_one, ← hsplit]
  exact heq

/-- Injectivity of `n ↦ α^n` below the group order — the form the meaning lemma uses. -/
theorem alpha_pow_injOn [IsDomain F] (α : F) (h : IsGen α) {m n : Nat} (hm : m < N) (hn : n < N)
    (heq : α ^ m = α ^ n) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | rfl | hlt
  · exact absurd (pow_sub_eq_one α (alpha_ne_zero α h) (le_of_lt hlt) heq.symm)
      (alpha_pow_ne_one α h (by omega) (by omega))
  · rfl
  · exact absurd (pow_sub_eq_one α (alpha_ne_zero α h) (le_of_lt hlt) heq)
      (alpha_pow_ne_one α h (by omega) (by omega))

end GF128
