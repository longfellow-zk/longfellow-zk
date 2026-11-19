import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Constructing the trace-dual basis

The Gram-matrix construction works for any basis. For a power basis, Mathlib's
minimal-polynomial quotient formula supplies the synthetic-division construction.
Both compute the same `Basis.traceDual` consumed by the protocol.
-/

namespace DualPacking

open Finset Module Polynomial
open scoped Classical

variable {K F I : Type*} [Field K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I]

/-- The columns of the inverse trace-pairing matrix, packed in the original basis. -/
noncomputable def gramDual (e : Basis I K F) (j : I) : F :=
  ∑ k, e k * algebraMap K F ((Algebra.traceMatrix K e)⁻¹ k j)

/-- Gram inversion computes the exact dual basis used by dual packing. -/
theorem traceDual_eq_gramDual (e : Basis I K F) :
    (fun j => e.traceDual j) = gramDual e := by
  apply Basis.traceDual_eq_iff.mpr
  intro j l
  let G := Algebra.traceMatrix K e
  have hdet : G.det ≠ 0 := by
    simpa only [G, Algebra.traceMatrix_of_basis] using det_traceForm_ne_zero e
  have hi := congrArg (fun M : Matrix I I K => M l j)
    (Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet))
  simp only [Matrix.mul_apply, Matrix.one_apply] at hi
  rw [Algebra.traceForm_apply, gramDual, sum_mul, map_sum]
  calc
    _ = ∑ k, G l k * G⁻¹ k j := by
      apply sum_congr rfl
      intro k _
      have ht : (e k * algebraMap K F (G⁻¹ k j)) * e l =
          (G⁻¹ k j) • (e l * e k) := by
        simp only [Algebra.smul_def]
        ring
      rw [ht, map_smul, smul_eq_mul, mul_comm]
      rfl
    _ = _ := hi

/-- Pairing checks identify an arbitrary proposed table with the canonical dual. -/
theorem traceDual_eq_of_pairings (e : Basis I K F) (a : I → F)
    (h : ∀ j l, Algebra.trace K F (a j * e l) = if l = j then 1 else 0) :
    (fun j => e.traceDual j) = a := by
  apply Basis.traceDual_eq_iff.mpr
  simpa only [Algebra.traceForm_apply] using h

/-- Synthetic division of the minimal polynomial gives the monomial-basis dual. -/
theorem powerBasis_traceDual (pb : PowerBasis K F) (j : Fin pb.dim) :
    pb.basis.traceDual j = (minpolyDiv K pb.gen).coeff j /
      aeval pb.gen (derivative (minpoly K pb.gen)) :=
  Basis.traceDual_powerBasis_eq pb j

omit [Fintype F] in
/-- The initial value for descending synthetic division. -/
theorem dual_quotient_leading (pb : PowerBasis K F) :
    (minpolyDiv K pb.gen).coeff (pb.dim - 1) = 1 := by
  have hd := natDegree_minpolyDiv_succ pb.isIntegral_gen
  rw [pb.natDegree_minpoly] at hd
  have he : (minpolyDiv K pb.gen).natDegree = pb.dim - 1 := by omega
  rw [← he]
  exact (minpolyDiv_monic pb.isIntegral_gen).coeff_natDegree

omit [Fintype F] in
/-- The descending synthetic-division recurrence, expressed for quotient coefficients. -/
theorem dual_quotient_recurrence (pb : PowerBasis K F) (j : ℕ) :
    (minpolyDiv K pb.gen).coeff j =
      algebraMap K F ((minpoly K pb.gen).coeff (j + 1)) +
      pb.gen * (minpolyDiv K pb.gen).coeff (j + 1) := by
  simpa only [mul_comm] using coeff_minpolyDiv K pb.gen j

/-- Finite fields are separable, so the denominator can always be inverted. -/
theorem dual_derivative_ne_zero (pb : PowerBasis K F) :
    aeval pb.gen (derivative (minpoly K pb.gen)) ≠ 0 :=
  (Algebra.IsSeparable.isSeparable K pb.gen).aeval_derivative_ne_zero
    (minpoly.aeval K pb.gen)

end DualPacking
