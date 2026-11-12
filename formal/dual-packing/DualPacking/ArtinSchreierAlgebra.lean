import DualPacking.Coordinates
import DualPacking.DualBasis
import DualPacking.Trace

/-! # Trace duality and adjoints over arbitrary finite fields

The trace pairing turns base-field queries into field inner products. Public
coefficient conversion is the trace adjoint of the base-field linear query map.
The masks used by the protocol are Artin--Schreier values `frobenius K F t - t`.
-/

namespace DualPacking.ArtinSchreier

open Finset Module
open scoped Classical

variable {K F I J : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
  [Fintype I] [DecidableEq I] [Fintype J]

omit [Fintype K] [Fintype F] [Fintype I] [DecidableEq I] in
theorem trace_mul_digit (e : Basis I K F) (x y : F) (k : I) :
    traceF K (x * digit e y k) = traceF K x * digit e y k :=
  trace_mul_base x (e.repr y k)

omit [Fintype K] [Fintype F] [DecidableEq I] in
/-- A public trace check is a fixed base-field linear form on the coordinates. -/
theorem trace_coordinates (e : Basis I K F) (x : F) :
    traceF K x = ∑ j, digit e x j * traceF K (e j) := by
  conv_lhs => rw [← reconstruct e x]
  rw [trace_sum]
  apply sum_congr rfl
  intro j _
  rw [trace_mul_digit, mul_comm]

omit [DecidableEq I] in
/-- The public Frobenius map can be evaluated by a fixed base-field matrix,
without generic exponentiation of the supplied element. -/
theorem frobenius_coordinates (e : Basis I K F) (x : F) :
    frobenius K F x = ∑ j, frobenius K F (e j) * digit e x j := by
  conv_lhs => rw [← reconstruct e x]
  rw [map_sum]
  apply sum_congr rfl
  intro j _
  rw [map_mul]
  change frobenius K F (e j) * frobenius K F (algebraMap K F (e.repr x j)) = _
  rw [(frobenius K F).commutes]
  rfl

/-- The trace-dual basis reads the canonical base-field coordinates of the original word. -/
theorem trace_dual (e : Basis I K F) (x : F) (j : I) :
    traceF K (e.traceDual j * x) = digit e x j := by
  have h := e.traceDual.traceDual_repr_apply x j
  simp only [Basis.traceDual_traceDual, Algebra.traceForm_apply] at h
  simpa [traceF, digit, mul_comm] using
    congrArg (algebraMap K F) h.symm

omit [Fintype K] [Fintype F] [DecidableEq I] in
/-- If the extension degree is nonzero in the base field, its inverse is a
public trace-one element. The protocol does not require this normalization. -/
theorem trace_inverse_degree (e : Basis I K F) (hm : (Fintype.card I : K) ≠ 0) :
    traceF K (algebraMap K F ((Fintype.card I : K)⁻¹)) = 1 := by
  unfold traceF
  rw [Algebra.trace_algebraMap, Module.finrank_eq_card_basis e, nsmul_eq_mul,
    mul_inv_cancel₀ hm, map_one]

/-- Public coordinate transpose, interpreted in the trace-dual basis. -/
noncomputable def coefficient (e : Basis I K F) (R : J → I → F)
    (i : J) (k : I) : F :=
  ∑ j, e.traceDual j * digit e (R i j) k

omit [Fintype J] in
/-- The computed Gram table gives exactly the protocol's public coefficients. -/
theorem coefficient_gramDual (e : Basis I K F) (R : J → I → F) (i : J) (k : I) :
    coefficient e R i k = ∑ j, gramDual e j * digit e (R i j) k := by
  unfold coefficient
  apply sum_congr rfl
  intro j _
  rw [show e.traceDual j = gramDual e j from congrFun (traceDual_eq_gramDual e) j]

noncomputable def forms (e : Basis I K F) (R : J → I → F)
    (X : J → F) (k : I) : F := ∑ i, coefficient e R i k * X i

/-- The original arbitrary base-field linear form; no tensor factorization is used. -/
noncomputable def value (e : Basis I K F) (R : J → I → F)
    (X : J → F) : F := ∑ i, ∑ j, R i j * digit e (X i) j

omit [Fintype J] in
theorem trace_coefficient_mul (e : Basis I K F) (R : J → I → F)
    (X : F) (i : J) (k : I) :
    traceF K (coefficient e R i k * X) =
      ∑ j, digit e (R i j) k * digit e X j := by
  rw [coefficient, sum_mul, trace_sum]
  apply sum_congr rfl
  intro j _
  have hm : e.traceDual j * digit e (R i j) k * X =
      (e.traceDual j * X) * digit e (R i j) k := by ring
  rw [hm, trace_mul_digit, trace_dual, mul_comm]

/-- End-to-end bridge from the public coefficient transpose to the canonical
base-field coordinates of the committed words. -/
theorem trace_forms (e : Basis I K F) (R : J → I → F)
    (X : J → F) (k : I) : traceF K (forms e R X k) = digit e (value e R X) k := by
  simp only [forms, value, trace_sum, trace_coefficient_mul, digit_sum, digit_mul_digit]

/-- A base-field query packed in the trace-dual basis. -/
noncomputable def dualPack (e : Basis I K F) (a : I → K) : F :=
  ∑ j, e.traceDual j * algebraMap K F (a j)

/-- The original base-field-valued query, on the canonical coordinates of the words. -/
noncomputable def baseValue (e : Basis I K F) (a : J → I → K)
    (X : J → F) : K := ∑ i, ∑ j, a i j * e.repr (X i) j

theorem trace_dualPack_mul (e : Basis I K F) (a : I → K) (x : F) :
    traceF K (dualPack e a * x) = algebraMap K F (∑ j, a j * e.repr x j) := by
  rw [dualPack, sum_mul, trace_sum, map_sum]
  apply sum_congr rfl
  intro j _
  have hm : e.traceDual j * algebraMap K F (a j) * x =
      (e.traceDual j * x) * algebraMap K F (a j) := by ring
  rw [hm, trace_mul_base, trace_dual]
  simp only [digit, map_mul, mul_comm]

/-- Dual packing preserves the complete base-field inner product in a single trace. -/
theorem trace_base_inner_product (e : Basis I K F) (a : J → I → K)
    (X : J → F) :
    traceF K (∑ i, dualPack e (a i) * X i) = algebraMap K F (baseValue e a X) := by
  simp only [trace_sum, trace_dualPack_mul, baseValue, map_sum]

/-- One base-field output gives exactly one trace-zero check; the target is lifted
with a trace-one element, which need not be the field element `1`. -/
theorem base_claim_iff_trace_zero (e : Basis I K F) (a : J → I → K)
    (X : J → F) (c : K) (rho : F) (hrho : traceF K rho = 1) :
    c = baseValue e a X ↔
      traceF K ((∑ i, dualPack e (a i) * X i) - rho * algebraMap K F c) = 0 := by
  rw [trace_sub, trace_base_inner_product, trace_mul_base, hrho, one_mul, sub_eq_zero]
  constructor
  · intro h
    exact congrArg (algebraMap K F) h.symm
  · intro h
    exact ((algebraMap K F).injective h).symm

/-- The same exact claim as a field equation with an Artin--Schreier witness. -/
theorem base_claim_iff_exists (e : Basis I K F) (a : J → I → K)
    (X : J → F) (c : K) (rho : F) (hrho : traceF K rho = 1) :
    c = baseValue e a X ↔ ∃ t : F,
      frobenius K F t - t = (∑ i, dualPack e (a i) * X i) - rho * algebraMap K F c := by
  rw [base_claim_iff_trace_zero e a X c rho hrho, trace_zero_iff_exists]

/-- The base-field linear map determined by one public coefficient row. -/
noncomputable def rowMap (e : Basis I K F) (R : I → F) (x : F) : F :=
  ∑ j, R j * digit e x j

/-- Pull a public test coefficient back through the base-field linear query map. -/
noncomputable def rowAdjoint (e : Basis I K F) (R : I → F) (y : F) : F :=
  ∑ j, e.traceDual j * traceF K (y * R j)

/-- The coefficient transformation is the adjoint for the trace pairing. -/
theorem trace_rowAdjoint (e : Basis I K F) (R : I → F) (x y : F) :
    traceF K (rowAdjoint e R y * x) = traceF K (y * rowMap e R x) := by
  simp only [rowAdjoint, rowMap, sum_mul, mul_sum, trace_sum]
  apply sum_congr rfl
  intro j _
  have hm : e.traceDual j * traceF K (y * R j) * x =
      (e.traceDual j * x) * traceF K (y * R j) := by ring
  rw [hm, trace_mul_trace, trace_dual, ← mul_assoc, trace_mul_digit]
  ring

omit [Fintype J] in
/-- The protocol's coefficient is exactly the adjoint applied to the output
coordinate functional, rather than a transpose interpreted in the wrong basis. -/
theorem coefficient_eq_rowAdjoint (e : Basis I K F) (R : J → I → F)
    (i : J) (k : I) : coefficient e R i k = rowAdjoint e (R i) (e.traceDual k) := by
  simp only [coefficient, rowAdjoint, trace_dual]

omit [Fintype J] in
/-- Each output coordinate uses precisely the single-base-field query packing. -/
theorem coefficient_eq_dualPack (e : Basis I K F) (R : J → I → F)
    (i : J) (k : I) :
    coefficient e R i k = dualPack e (fun j => e.repr (R i j) k) := rfl

end DualPacking.ArtinSchreier
