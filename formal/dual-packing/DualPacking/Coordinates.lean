import Mathlib

/-! # Canonical field coordinates for trace-pairing dual packing

The algebra works over any field extension. The binary protocol specializes the
base field `K` to `ZMod 2`; no separately supplied bit variables are used.
-/

namespace DualPacking

open Finset Module
open scoped Classical

section General

variable {K F I J : Type*} [Field K] [Field F] [Algebra K F]
  [Fintype I] [Fintype J]

/-- Canonical basis coordinate, embedded back into the extension field. -/
noncomputable def digit (e : Basis I K F) (x : F) (k : I) : F :=
  algebraMap K F (e.repr x k)

omit [Fintype I] in
theorem digit_add (e : Basis I K F) (x y : F) (k : I) :
    digit e (x + y) k = digit e x k + digit e y k := by
  simp [digit]

omit [Fintype I] in
theorem digit_sum (e : Basis I K F) (x : J → F) (k : I) :
    digit e (∑ j, x j) k = ∑ j, digit e (x j) k := by
  simp [digit, map_sum, Finsupp.finsetSum_apply]

omit [Fintype I] in
theorem digit_mul_base (e : Basis I K F) (x : F) (c : K) (k : I) :
    digit e (x * algebraMap K F c) k = digit e x k * algebraMap K F c := by
  rw [mul_comm x, ← Algebra.smul_def]
  simp [digit, mul_comm]

theorem reconstruct (e : Basis I K F) (x : F) :
    (∑ k, e k * digit e x k) = x := by
  simpa [digit, Algebra.smul_def, mul_comm] using e.sum_repr x

theorem digit_pack (e : Basis I K F) (c : I → K) (k : I) :
    digit e (∑ j, e j * algebraMap K F (c j)) k = algebraMap K F (c k) := by
  have h := congrArg (fun v => algebraMap K F (v k)) (e.repr_sum_self c)
  simpa [digit, Algebra.smul_def, mul_comm] using h

omit [Fintype I] in
/-- Multiplying by an embedded coordinate is base-field scaling. -/
theorem digit_mul_digit (e : Basis I K F) (x y : F) (j k : I) :
    digit e (x * digit e y j) k = digit e x k * digit e y j :=
  digit_mul_base e x (e.repr y j) k

/-- Extension-field size derived from the actual coordinate equivalence. -/
theorem extension_card [Fintype K] [Fintype F] (e : Basis I K F) :
    Fintype.card F = Fintype.card K ^ Fintype.card I := by
  simpa using Fintype.card_congr e.equivFun.toEquiv

end General

section Binary

variable {F I : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype I]

omit [Fintype I] in
/-- The canonical coordinates of every packed field element really are bits. -/
theorem canonical_bit (e : Basis I (ZMod 2) F) (x : F) (k : I) :
    digit e x k = 0 ∨ digit e x k = 1 := by
  unfold digit
  generalize e.repr x k = c
  fin_cases c
  · exact Or.inl (map_zero (algebraMap (ZMod 2) F))
  · exact Or.inr (map_one (algebraMap (ZMod 2) F))

/-- The field size follows from the supplied binary basis, rather than being
assumed as a separate, potentially disconnected numerical premise. -/
theorem binary_card [Fintype F] (e : Basis I (ZMod 2) F) :
    Fintype.card F = 2 ^ Fintype.card I := by
  have h := Fintype.card_congr e.equivFun.toEquiv
  simpa using h

end Binary
end DualPacking
