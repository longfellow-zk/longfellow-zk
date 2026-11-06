import LfzkV2.Current.Adapter
import ECDSA.Pratt

/-! Exact current mdoc adapter arithmetic. This is a component certificate,
not the complete application or Polygero soundness certificate. -/
namespace LfzkV2.Current.Adapter.Mdoc
open scoped Classical

def binaryOrder : ℕ := 2^128
def primeOrder : ℕ := 2^256 - 2^224 + 2^192 + 2^96 - 1
def groupOrder : ℕ := binaryOrder - 1
def inputBits : ℕ := 768 + 256
def quotientBound : ℕ := 2^10
def generatorExponent : ℕ := groupOrder - 2^64

/-- Rust uses `g = X^(M-2^64)`. This exponent preserves the primitive order. -/
theorem generator_order {G : Type} [Group G] (x : G) (hx : orderOf x = groupOrder) :
    orderOf (x ^ generatorExponent) = groupOrder := by
  have h : (orderOf x).Coprime generatorExponent := by
    rw [hx]
    norm_num [groupOrder, binaryOrder, generatorExponent, Nat.Coprime]
  simpa only [hx] using h.orderOf_pow

/-- The quotient-tree base X really is g^(-p), using the coordinate prime. -/
theorem quotient_base {G : Type} [Group G] (x : G) (hx : orderOf x = groupOrder) :
    (x ^ generatorExponent) ^ (-(primeOrder : ℤ)) = x := by
  rw [← zpow_natCast x generatorExponent, ← zpow_mul]
  conv_rhs => rw [← zpow_one x]
  rw [zpow_eq_zpow_iff_modEq, hx]
  norm_num [Int.ModEq, generatorExponent, groupOrder, binaryOrder, primeOrder]

theorem prime_prime : primeOrder.Prime := by
  convert ECDSA.prime_115792089210356248762697446949407573530086143415290314195533631308867097853951
    using 1
  norm_num [primeOrder]

instance : Fact primeOrder.Prime := ⟨prime_prime⟩

def collisionBound : ℚ :=
  ((2 * (quotientBound * primeOrder / groupOrder) + 1 : ℕ) : ℚ)^2 /
    ((primeOrder - 1 : ℕ) : ℚ)^2

/-- A little slack keeps the coefficient readable. The exact prime-field
denominator remains in `collisionBound`; no `p=2^256` approximation is used. -/
theorem collisionBound_le : collisionBound ≤ 4198401 / (binaryOrder : ℚ)^2 := by
  norm_num [collisionBound, quotientBound, primeOrder, groupOrder, binaryOrder]

theorem conversion_probability_le (weights : Fin inputBits → ZMod primeOrder)
    (values : Fin inputBits → Bool) (target : ZMod primeOrder)
    (hfalse : residual weights values target ≠ 0) :
    ((Finset.univ.filter fun a : Linear.TerminalSampling.Nonzero (ZMod primeOrder) ×
        Linear.TerminalSampling.Nonzero (ZMod primeOrder) =>
      Bad weights values target groupOrder quotientBound a.1 ∧
        Bad weights values target groupOrder quotientBound a.2).card : ℚ) /
        Fintype.card (Linear.TerminalSampling.Nonzero (ZMod primeOrder) ×
          Linear.TerminalSampling.Nonzero (ZMod primeOrder)) ≤
      4198401 / (binaryOrder : ℚ)^2 := by
  apply (two_bad_probability_le weights values target
    (M := groupOrder) (K := quotientBound) (by norm_num [groupOrder, binaryOrder])
    (by norm_num [inputBits, quotientBound]) hfalse).trans
  exact collisionBound_le

end LfzkV2.Current.Adapter.Mdoc
