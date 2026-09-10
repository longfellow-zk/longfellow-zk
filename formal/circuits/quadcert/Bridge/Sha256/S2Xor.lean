/-
# Joining the template's xor mids to `SHA/Sigma.lean`

`Core/ConeXor.lean` shows a xor mid is bit-valued, in the field. `SHA/Sigma.lean` expands `σ₀`
and `σ₁` into `SHA256.xb`, on `Nat`. This file is the one equation between them.

It is deliberately tiny and deliberately separate: `Core/` may not depend on `SHA/`, and the two
sides were developed against different vocabularies -- `Quadcert.xorVal` over `F`, `SHA256.xb`
over `Nat`. Everything downstream of step 2 goes through `xorVal_cast`.
-/

import quadcert.Core.ConeXor
import SHA.Sigma
import SHA.Field
import SHA.Pack

namespace Sha256Blk

variable {F : Type} [Field F]

/-- The field xor of two cast bits is the cast of the `Nat` xor. -/
theorem xorVal_cast {a b : Nat} (ha : SHA256.IsBit a) (hb : SHA256.IsBit b) :
    Quadcert.xorVal ((a : Nat) : F) ((b : Nat) : F) = ((SHA256.xb a b : Nat) : F) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [Quadcert.xorVal, SHA256.xb]

/-- The form a schedule meaning lemma uses: a field value known to be a bit *is* the cast of a
    `Nat` bit, and `xorVal` commutes with that identification. -/
theorem xorVal_eq_cast {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    ∃ a b : Nat, SHA256.IsBit a ∧ SHA256.IsBit b ∧ x = (a : F) ∧ y = (b : F) ∧
      Quadcert.xorVal x y = ((SHA256.xb a b : Nat) : F) := by
  obtain ⟨a, ha, rfl⟩ := SHA256F.isBit_cast x hx
  obtain ⟨b, hb, rfl⟩ := SHA256F.isBit_cast y hy
  exact ⟨a, b, ha, hb, rfl, rfl, xorVal_cast ha hb⟩

/-- Naming the bit of a xor: `natBit` commutes with `xorVal`. This is the equation the σ join
    runs on — the left side is what a group entry evaluates to, the right side is what
    `sigma0_bits` produces. -/
theorem natBit_xorVal {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    SHA256F.natBit (Quadcert.xorVal x y) = SHA256.xb (SHA256F.natBit x) (SHA256F.natBit y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp only [Quadcert.xorVal, SHA256F.natBit_zero, SHA256F.natBit_one, SHA256.xb] <;>
    norm_num [SHA256F.natBit_zero, SHA256F.natBit_one]

/-- `chVal` on cast bits is the cast of `SHA256.chb`. -/
theorem natBit_chVal {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    SHA256F.natBit (Quadcert.chVal x y z)
      = SHA256.chb (SHA256F.natBit x) (SHA256F.natBit y) (SHA256F.natBit z) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp only [Quadcert.chVal, SHA256.chb, SHA256.xb, SHA256F.natBit] <;> norm_num

/-- `majVal` on cast bits is the cast of `SHA256.majb`. -/
theorem natBit_majVal {x y z : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (hz : z = 0 ∨ z = 1) :
    SHA256F.natBit (Quadcert.majVal x y z (Quadcert.xorVal x y))
      = SHA256.majb (SHA256F.natBit x) (SHA256F.natBit y) (SHA256F.natBit z) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp only [Quadcert.majVal, Quadcert.xorVal, SHA256.majb, SHA256.xb, SHA256F.natBit] <;>
    norm_num

end Sha256Blk
