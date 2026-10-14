import polygero.Algebra.PolynomialChallenges.Basic

/-!
# Exact polynomial agreement

The exact (non-robust) agreement calculation is only a degree argument.  This
module records it independently of evaluation-code wraparound: multiplication
by `X^s` already detects whether a polynomial has degree at least `d`.
-/

namespace RecursivePolygero.Local

open Polynomial

variable {F : Type*} [Field F]
variable {d s : ℕ}

/-- Multiplication by the top-degree allowed challenge detects membership in
the lower-degree polynomial space. -/
theorem mem_degreeLT_of_X_pow_mul_mem_degreeLT
    {f : F[X]} (hproduct : X ^ s * f ∈ degreeLT F (d + s)) :
    f ∈ degreeLT F d := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero] at hproduct ⊢
  intro i hi
  simpa [Polynomial.coeff_X_pow_mul] using hproduct (i + s) (by omega)

end RecursivePolygero.Local
