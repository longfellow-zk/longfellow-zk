import Mathlib.Algebra.CharP.Basic
import Mathlib.Tactic.LinearCombination
import SHA.Bits

/-!
# The wrapping-sum assertion

`assert_wrapping_sum_prime` (`analog_adder/src/circuit.rs:113`) is the only assertion family in
the SHA-256 circuit with any content; the other 6,656 are booleanity. It builds

* `p`, the expected word, as the field element `Σ_j 2 ^ j · bit_j`;
* `c`, the same linear form summed over the `n` addend words;
* `z = c - p`,

and asserts `∏_{i < n} (z - i · 2 ^ 32) = 0`. Measured on the artifact, `n` is 2 for the eight
`final` assertions, 4 for the 48 `schedule` ones, and for the 128 `round_step` ones it is 6 for
the 64 that constrain `e` (`d + h + Σ₁e + Ch efg + Kt + Wt`) and 7 for the 64 that constrain `a`
(the same, with `d` replaced by `Σ₀a + Maj abc`) — see `SHA/Sound.lean`. The
product is a balanced tree padded with `1`s — so nothing here may assume a particular `n` or a
particular association, and `wrapPoly` is stated by recursion with the instances matching it up
to `ring`.

The assertion is *not* by itself the statement that the sum wraps correctly. It says `z` is one
of `n` permitted multiples of `2 ^ 32`, which pins `c ≡ p (mod 2 ^ 32)` only once the addends are
known to be sums of genuine bits (booleanity, supplied separately) and the field is known to be
too large for the sum to wrap the characteristic. That second condition is what
`assert_wrapping_sum` checks at compile time via `pseudo_dimension_of_multiplicative_group`, and
it reappears here as `hnp` — an honest hypothesis rather than something the circuit proves.
-/

namespace SHA256F

variable {F : Type} [Field F]

/-- `∏_{i < n} (z - i · t)`, by recursion rather than over `List.range`, so that the induction in
    `wrap_of_prod_zero` peels one factor without list surgery. -/
def wrapPoly : Nat → F → F → F
  | 0, _, _ => 1
  | n + 1, t, z => (z - (n : F) * t) * wrapPoly n t z

/-- The whole content of the assertion, in a field: a product vanishes only at a factor. -/
theorem wrap_of_prod_zero :
    ∀ (n : Nat) (t z : F), wrapPoly n t z = 0 → ∃ i, i < n ∧ z = (i : F) * t
  | 0, t, z, h => absurd h one_ne_zero
  | n + 1, t, z, h => by
      rw [wrapPoly] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact ⟨n, Nat.lt_succ_self n, by linear_combination h'⟩
      · obtain ⟨i, hi, hz⟩ := wrap_of_prod_zero n t z h'
        exact ⟨i, Nat.lt_succ_of_lt hi, hz⟩

/-- Naturals below the characteristic are told apart by their images. This is the step that makes
    a field equation a statement about 32-bit arithmetic, and the only one that needs `CharP`. -/
theorem cast_inj_of_lt {p : Nat} [CharP F p] {a b : Nat} (ha : a < p) (hb : b < p)
    (h : (a : F) = (b : F)) : a = b :=
  CharP.natCast_injOn_Iio F p (Set.mem_Iio.mpr ha) (Set.mem_Iio.mpr hb) h

/-- The `Nat` reading of the assertion: the expected word is the sum of the addends reduced
    mod `2 ^ 32`.

    `hC` is discharged by the addends being `n` words each below `2 ^ 32`, `hP` by the expected
    word being one, and `hnp` by the characteristic being a 256-bit prime against an `n · 2 ^ 32`
    that never exceeds `2 ^ 35`. -/
theorem wrap_nat {p : Nat} [CharP F p] (n C P : Nat)
    (hC : C < n * 2 ^ 32) (hP : P < 2 ^ 32) (hnp : n * 2 ^ 32 ≤ p)
    (h : ∃ i, i < n ∧ (C : F) - (P : F) = (i : F) * ((2 ^ 32 : Nat) : F)) :
    P = C % 2 ^ 32 := by
  obtain ⟨i, hi, hz⟩ := h
  have hlt : P + i * 2 ^ 32 < n * 2 ^ 32 := by
    have hstep : (i + 1) * 2 ^ 32 ≤ n * 2 ^ 32 := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, Nat.one_mul] at hstep
    omega
  have hcast : ((C : Nat) : F) = ((P + i * 2 ^ 32 : Nat) : F) := by
    push_cast
    linear_combination hz
  have := cast_inj_of_lt (p := p) (by omega) (by omega) hcast
  omega

/-- The two halves composed, in the form a generated meaning lemma will cite: the circuit's own
    product node is zero, therefore the expected word is the wrapped sum. -/
theorem wrap_sum_of_zero {p : Nat} [CharP F p] (n C P : Nat) (z : F)
    (hC : C < n * 2 ^ 32) (hP : P < 2 ^ 32) (hnp : n * 2 ^ 32 ≤ p)
    (hz : z = (C : F) - (P : F))
    (hroot : wrapPoly n ((2 ^ 32 : Nat) : F) z = 0) :
    P = C % 2 ^ 32 := by
  obtain ⟨i, hi, hiz⟩ := wrap_of_prod_zero n _ z hroot
  exact wrap_nat n C P hC hP hnp ⟨i, hi, by rw [← hz, hiz]⟩

end SHA256F
