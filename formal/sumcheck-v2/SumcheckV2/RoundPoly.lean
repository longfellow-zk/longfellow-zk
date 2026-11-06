import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# V2 projective round polynomials

`rust/runtime/v2/proto/src/sumcheck.rs` transmits the constant and linear
coefficients of a quadratic. The projective sum is `c0 + c2`, so the incoming
claim determines the omitted coefficient. These definitions work over every
field, including characteristic two; no interpolation nodes are required.
-/

namespace SumcheckV2

open Polynomial

/-- The two unmasked coefficients carried by one v2 round message. -/
structure RoundPoly (F : Type) where
  c0 : F
  c1 : F
  deriving DecidableEq

variable {F : Type} [Field F]

/-- Sum over the projective endpoints `0, infinity` of a quadratic. -/
def projectiveSum (P : Polynomial F) : F := P.coeff 0 + P.coeff 2

namespace RoundPoly

/-- The incoming claim supplies `c2 = claim - c0`. -/
noncomputable def toPoly (p : RoundPoly F) (claim : F) : Polynomial F :=
  C (claim - p.c0) * X ^ 2 + C p.c1 * X + C p.c0

/-- The update used by both `prover::round` and `PadExpression::round`. -/
def eval (p : RoundPoly F) (claim z : F) : F :=
  z ^ 2 * claim + (1 - z ^ 2) * p.c0 + z * p.c1

@[simp] theorem coeff_zero (p : RoundPoly F) (claim : F) :
    (p.toPoly claim).coeff 0 = p.c0 := by
  simp only [toPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

@[simp] theorem coeff_one (p : RoundPoly F) (claim : F) :
    (p.toPoly claim).coeff 1 = p.c1 := by
  simp only [toPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

@[simp] theorem coeff_two (p : RoundPoly F) (claim : F) :
    (p.toPoly claim).coeff 2 = claim - p.c0 := by
  simp only [toPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

@[simp] theorem projectiveSum_toPoly (p : RoundPoly F) (claim : F) :
    projectiveSum (p.toPoly claim) = claim := by simp [projectiveSum]

theorem toPoly_natDegree (p : RoundPoly F) (claim : F) :
    (p.toPoly claim).natDegree ≤ 2 := Polynomial.natDegree_quadratic_le

@[simp] theorem eval_toPoly (p : RoundPoly F) (claim z : F) :
    (p.toPoly claim).eval z = p.eval claim z := by
  simp only [toPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, eval]
  ring

/-- Honest transmission is by coefficients, even over a two-element field. -/
def ofPoly (P : Polynomial F) : RoundPoly F := ⟨P.coeff 0, P.coeff 1⟩

theorem toPoly_ofPoly (P : Polynomial F) (hdeg : P.natDegree ≤ 2) :
    (ofPoly P).toPoly (projectiveSum P) = P := by
  have h := P.as_sum_range_C_mul_X_pow' (n := 3) (by omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one] at h
  rw [toPoly, ofPoly, projectiveSum]
  simp only [add_sub_cancel_left]
  calc
    _ = C (P.coeff 0) + C (P.coeff 1) * X + C (P.coeff 2) * X ^ 2 := by ring
    _ = P := h.symm

theorem eval_ofPoly (P : Polynomial F) (hdeg : P.natDegree ≤ 2) (z : F) :
    (ofPoly P).eval (projectiveSum P) z = P.eval z := by
  rw [← eval_toPoly, toPoly_ofPoly P hdeg]

/-- A false projective sum forces a nonzero difference polynomial. -/
theorem toPoly_sub_ne_zero (P : Polynomial F) (p : RoundPoly F) (claim : F)
    (hfalse : claim ≠ projectiveSum P) : p.toPoly claim - P ≠ 0 := by
  intro h
  have heq := congrArg projectiveSum (sub_eq_zero.mp h)
  exact hfalse (by simpa using heq)

end RoundPoly

end SumcheckV2
