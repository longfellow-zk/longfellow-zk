import GF128.Cone

/-!
# The bit layer: what the artifact's booleanity assertions give, and the five forms

The `Sha256Gf2` artifact has exactly **two** assertion shapes, and nothing else:

| shape | count | reading |
|---|---:|---|
| `1·(one·b) + 1·(b·b)` | 6,656 | `b + b² = 0`, i.e. `b` is a bit |
| `1·(x·y)` | 184 | the wrapping-sum product vanishes |

`Gf2Wrap.lean` handles the second. This file handles what the first gives, and the five forms
that consume it.

An injection factor injects a *bit*, but not always a witnessed one: `algsimp` fused the round's
logic into the factor, so the injected value is a polynomial in the bit wires. Measured over all
431 injection cones by evaluating each row's form at every boolean assignment of its wires —
24,960 factors, and exactly five functions occur:

| form | count | what it is |
|---|---:|---|
| `b` | 13,696 | a witnessed bit |
| `b₁ + b₂ + b₃` | 6,544 | `Σ₀ Σ₁ σ₀ σ₁`, three-way xor |
| `b₁ + b₂` | 624 | the same, at the bit positions where a shift kills the third leg |
| `a·b + c + a·c` | 2,048 | `Ch(a,b,c)` = 64 rounds × 32 bits |
| `a·b + b·c + a·c` | 2,048 | `Maj(a,b,c)` = 64 rounds × 32 bits |

The artifact spells these in **29** distinct operand orders, which cost nothing: an injection
row's value is a `List.sum`, so the order is not part of the statement.

Characteristic 2 is carrying the xor forms. Unlike the prime-field bridge there is no
`a + b − 2ab` to unfold: addition *is* xor, so `bit_xor2` is eight lines of case analysis rather
than a `Nat` argument about carries.
-/

open scoped Classical

namespace Sha256Gf2

open GF128

variable {F : Type} [Field F] [CharP F 2]

/-! ## Reading a bit back as a `Nat` -/

/-- A field element known to be a bit, read as a `Nat`. Noncomputable because `F` carries no
    `DecidableEq`; only its *value* on `0` and `1` is ever used. -/
noncomputable def bitOf (x : F) : Nat := if x = 1 then 1 else 0

theorem bitOf_isBit (x : F) : bitOf x = 0 ∨ bitOf x = 1 := by
  unfold bitOf; split <;> simp

theorem bitOf_one : bitOf (1 : F) = 1 := by simp [bitOf]

theorem bitOf_zero : bitOf (0 : F) = 0 := by simp [bitOf]

/-- **The cast back.** For a value the circuit has asserted to be a bit, `bitOf` is a section of
    `Nat.cast`. This is what lets an injection cone's `n : Nat → Nat` be *defined* rather than
    assumed: `n j := bitOf (row j)`. -/
theorem bitOf_cast {x : F} (h : x = 0 ∨ x = 1) : ((bitOf x : Nat) : F) = x := by
  rcases h with rfl | rfl
  · simp [bitOf_zero]
  · simp [bitOf_one]

/-! ## What the booleanity assertion says -/

/-- **The 6,656 booleanity assertions.** The artifact asserts `b + b·b = 0`; in a field that is
    `b·(1 + b) = 0`, and in characteristic 2 the second root is `1` rather than `−1`. -/
theorem isBit_of_zero {b : F} (h : b + b * b = 0) : b = 0 ∨ b = 1 := by
  have h' : b * (1 + b) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by linear_combination h1 - CharTwo.add_self_eq_zero (1 : F))

/-! ## The five forms are bits

Each is a finite case analysis; `CharTwo.add_self_eq_zero` is the only field fact used, and it is
the one the prime field does not have. -/

theorem bit_xor2 {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x + y = 0 ∨ x + y = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

theorem bit_xor3 {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    x + y + z = 0 ∨ x + y + z = 1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

/-- `Ch(a,b,c) = a·b + (1+a)·c`, expanded. 2,048 factors: 64 rounds × 32 bits. -/
theorem bit_ch {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    a * b + c + a * c = 0 ∨ a * b + c + a * c = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

/-- `Maj(a,b,c) = a·b + b·c + a·c`. 2,048 factors. At `a = b = c = 1` this is `1 + 1 + 1 = 1`,
    which is where characteristic 2 does the work. -/
theorem bit_maj {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    a * b + b * c + a * c = 0 ∨ a * b + b * c + a * c = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

/-! ## …and what they mean as `Nat`

The word layer needs the arithmetic reading, not just booleanity. These are stated against the
`Nat` operations the SHA-256 specification uses. -/

theorem bitOf_xor2 {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    bitOf (x + y) = bitOf x ^^^ bitOf y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [bitOf_zero, bitOf_one, CharTwo.add_self_eq_zero]

theorem bitOf_xor3 {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    bitOf (x + y + z) = bitOf x ^^^ bitOf y ^^^ bitOf z := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp [bitOf_zero, bitOf_one, CharTwo.add_self_eq_zero]

theorem bitOf_ch {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    bitOf (a * b + c + a * c) = if bitOf a = 1 then bitOf b else bitOf c := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [bitOf_zero, bitOf_one, CharTwo.add_self_eq_zero]

theorem bitOf_maj {a b c : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1) :
    bitOf (a * b + b * c + a * c)
      = if bitOf a + bitOf b + bitOf c ≤ 1 then 0 else 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp [bitOf_zero, bitOf_one, CharTwo.add_self_eq_zero]

end Sha256Gf2
