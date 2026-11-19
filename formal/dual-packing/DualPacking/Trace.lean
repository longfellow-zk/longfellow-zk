import Mathlib.FieldTheory.Finite.Trace

/-! # Relative traces and additive Hilbert 90 for arbitrary finite fields

`frobenius K F` is the actual `|K|`-power automorphism. Its difference from the
identity has image exactly the kernel of the relative trace. No characteristic
or extension-degree restriction is imposed beyond the finite-field instances.
-/

namespace DualPacking.ArtinSchreier

open Finset Module
open scoped Classical

variable {K F J : Type*} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype J]

/-- The actual relative field trace, embedded into the extension field. -/
noncomputable def traceF (K : Type*) [Field K] [Algebra K F] (x : F) : F :=
  algebraMap K F (Algebra.trace K F x)

/-- The actual base-field Frobenius automorphism, not an assumed linear map. -/
noncomputable def frobenius (K F : Type*) [Field K] [Fintype K] [Field F] [Fintype F]
    [Algebra K F] : F ≃ₐ[K] F :=
  FiniteField.frobeniusAlgEquivOfAlgebraic K F

theorem frobenius_apply (x : F) : frobenius K F x = x ^ Fintype.card K := rfl

omit [Fintype K] [Fintype F] in
theorem trace_add (x y : F) : traceF K (x + y) = traceF K x + traceF K y := by
  simp [traceF]

omit [Fintype K] [Fintype F] in
theorem trace_sub (x y : F) : traceF K (x - y) = traceF K x - traceF K y := by
  simp [traceF]

omit [Fintype K] [Fintype F] in
theorem trace_sum (x : J → F) : traceF K (∑ j, x j) = ∑ j, traceF K (x j) := by
  simp [traceF, map_sum]

theorem trace_frobenius (x : F) : traceF K (frobenius K F x) = traceF K x := by
  exact congrArg (algebraMap K F) (Algebra.trace_eq_of_algEquiv (frobenius K F) x)

theorem trace_mask (x : F) : traceF K (frobenius K F x - x) = 0 := by
  rw [trace_sub, trace_frobenius, sub_self]

omit [Fintype K] [Fintype F] in
theorem trace_mul_base (x : F) (a : K) :
    traceF K (x * algebraMap K F a) = traceF K x * algebraMap K F a := by
  rw [mul_comm x, ← Algebra.smul_def]
  simp [traceF, mul_comm]

omit [Fintype K] [Fintype F] in
/-- A relative trace value is a base-field scalar. -/
theorem trace_mul_trace (x y : F) :
    traceF K (x * traceF K y) = traceF K x * traceF K y :=
  trace_mul_base x (Algebra.trace K F y)

omit [Fintype K] [Fintype F] in
theorem trace_mem_base (x : F) : ∃ a : K, algebraMap K F a = traceF K x :=
  ⟨Algebra.trace K F x, rfl⟩

theorem exists_trace_one : ∃ rho : F, traceF K rho = 1 := by
  obtain ⟨rho, hrho⟩ := Algebra.trace_surjective K F 1
  exact ⟨rho, by simp [traceF, hrho]⟩

theorem trace_pow_sum (x : F) :
    traceF K x = ∑ s ∈ range (finrank K F), x ^ (Fintype.card K ^ s) := by
  simpa [traceF, Nat.card_eq_fintype_card] using
    FiniteField.algebraMap_trace_eq_sum_pow K F x

-- Preserve the existing public Fintype argument after narrowing imports.
set_option linter.unusedSectionVars false in
omit [Fintype K] in
theorem trace_one : traceF K (1 : F) = (finrank K F : F) := by
  have h := Algebra.trace_algebraMap (R := K) (S := F) (1 : K)
  simpa [traceF] using congrArg (algebraMap K F) h

theorem trace_pairing_nondegenerate (x : F) (hx : x ≠ 0) :
    ∃ y : F, traceF K (x * y) = 1 := by
  obtain ⟨rho, hrho⟩ := exists_trace_one (K := K) (F := F)
  exact ⟨rho / x, by rw [mul_div_cancel₀ _ hx]; exact hrho⟩

/-- The fixed elements of the actual relative Frobenius are exactly the base field. -/
theorem frobenius_fixed_iff (x : F) :
    frobenius K F x = x ↔ ∃ a : K, algebraMap K F a = x := by
  constructor
  · intro hx
    have hp : ∀ n : ℕ, ((frobenius K F) ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
    apply IntermediateField.mem_bot.mp
    apply (IsGalois.mem_bot_iff_fixed x).mpr
    intro g
    obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K F).surjective g
    exact hp n.1
  · rintro ⟨a, rfl⟩
    exact (frobenius K F).commutes a

/-- The generalized Artin--Schreier map is a base-field linear map. -/
noncomputable def artinSchreierMap : F →ₗ[K] F :=
  (frobenius K F).toLinearMap - LinearMap.id

/-- Its kernel is precisely the one-dimensional base-field subspace. -/
theorem artinSchreier_ker :
    LinearMap.ker (artinSchreierMap : F →ₗ[K] F) = Submodule.span K {(1 : F)} := by
  ext t
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  change frobenius K F t - t = 0 ↔ ∃ a : K, a • (1 : F) = t
  rw [sub_eq_zero, frobenius_fixed_iff]
  simp only [Algebra.smul_def, mul_one]

/-- Additive Hilbert 90, proved from the actual Frobenius and relative trace. -/
theorem trace_zero_iff_exists (x : F) :
    traceF K x = 0 ↔ ∃ t : F, frobenius K F t - t = x := by
  let a : F →ₗ[K] F := artinSchreierMap
  let tr := Algebra.trace K F
  have hle : LinearMap.range a ≤ LinearMap.ker tr := by
    rintro _ ⟨t, rfl⟩
    apply (algebraMap K F).injective
    simpa [a, artinSchreierMap, traceF] using trace_mask (K := K) t
  have hak : finrank K (LinearMap.ker a) = 1 := by
    rw [show a = artinSchreierMap from rfl, artinSchreier_ker]
    exact finrank_span_singleton one_ne_zero
  have htr : finrank K (LinearMap.range tr) = 1 := by
    rw [LinearMap.range_eq_top.mpr (Algebra.trace_surjective K F)]
    simp
  have hd : finrank K (LinearMap.range a) = finrank K (LinearMap.ker tr) := by
    have ha := LinearMap.finrank_range_add_finrank_ker a
    have ht := LinearMap.finrank_range_add_finrank_ker tr
    omega
  have he := Submodule.eq_of_le_of_finrank_eq hle hd
  have hm : traceF K x = 0 ↔ x ∈ LinearMap.ker tr := by
    change algebraMap K F (tr x) = 0 ↔ tr x = 0
    exact map_eq_zero_iff _ (algebraMap K F).injective
  rw [hm, ← he, LinearMap.mem_range]
  rfl

end DualPacking.ArtinSchreier
