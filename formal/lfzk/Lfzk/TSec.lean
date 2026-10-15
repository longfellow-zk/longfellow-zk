import Lfzk.CompiledZkProfileRows

/-!
# T-security without reserving half the transcript-query coefficient

For tA ≤ G, bound tA² by G·tA and charge the mixed tA·N term to N. Above G,
the probability bound 1 suffices. Taking G = 2^λ avoids the old conversion's unnecessarily
large cutoff and its condition κ ≤ 2^(-λ-1). All three remaining inequalities are exact rational
checks at a concrete row. This lemma also supports the two-field Merkle multiplicity k = 2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TSec

/-- A linear majorant for the adaptive Merkle numerator on tA ≤ G. -/
theorem adaptiveNumerator_le_linear {fc tA L N G : ℕ} (ht : tA ≤ G) :
    Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) ≤
      fc * (1 + L) + N * (fc + G) + tA * (3 * G + 2 * fc + 1 + L) := by
  have hsq : tA * tA ≤ tA * G := Nat.mul_le_mul_left tA ht
  have hcross : tA * N ≤ G * N := Nat.mul_le_mul_right N ht
  have h := adaptiveNumerator_le_poly fc tA (L + N)
  nlinarith

/-- **T-security from three exact slack checks.** No assumption on the query budgets remains. -/
theorem tsec_of_linear_slack {p A K ε δ k : ℚ} {fc L N tA G : ℕ}
    (hp1 : p ≤ 1)
    (hp : p ≤ A + N * K + k * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) * δ)
    (hδ : 0 ≤ δ) (hk : 0 ≤ k) (hε : 0 ≤ ε)
    (hA : A + k * (fc * (1 + L) : ℕ) * δ ≤ ε)
    (hK : K + k * (fc + G : ℕ) * δ ≤ ε)
    (hT : k * (3 * G + 2 * fc + 1 + L : ℕ) * δ ≤ ε)
    (hG : 1 ≤ (G : ℚ) * ε) :
    p ≤ (1 + N + tA) * ε := by
  by_cases ht : tA ≤ G
  · have hcount : (Bcs.AdaptiveCommit.adaptiveNumerator fc tA (L + N) : ℚ) ≤
        (fc * (1 + L) : ℕ) + N * (fc + G : ℕ)
          + tA * (3 * G + 2 * fc + 1 + L : ℕ) := by
      exact_mod_cast adaptiveNumerator_le_linear (fc := fc) (L := L) (N := N) ht
    have hmerkle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hk) hδ
    have hquery := mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg N : (0 : ℚ) ≤ N)
    have hcommit := mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg tA : (0 : ℚ) ≤ tA)
    nlinarith
  · have hgt : (G : ℚ) ≤ tA := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge ht))
    calc p ≤ 1 := hp1
      _ ≤ (G : ℚ) * ε := hG
      _ ≤ (1 + N + tA) * ε :=
        mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℚ) N; linarith) hε

end Lfzk.TSec
