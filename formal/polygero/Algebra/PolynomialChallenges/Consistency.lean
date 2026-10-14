import polygero.Algebra.PolynomialChallenges.Basic
import Mathlib.FieldTheory.Finiteness

/-! The vector space of challenges consistent on a fixed set. -/
namespace RecursivePolygero.Local
open Polynomial Finset Codes
variable {F : Type*} [Field F] {n R m s : ℕ}

/-- The linear space of challenges admitting a response on the given set. -/
noncomputable def consistentChallenges
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) :
    Submodule F (Challenge F m s) where
  carrier := {B | AgreesOn C W S B}
  zero_mem' := ⟨0, by intro j _; simp [response]⟩
  add_mem' := by
    rintro B B' ⟨p, hp⟩ ⟨p', hp'⟩
    refine ⟨p + p', ?_⟩
    intro j hj
    simpa [response, add_mul, Finset.sum_add_distrib] using congrArg₂ (· + ·) (hp j hj) (hp' j hj)
  smul_mem' := by
    rintro a B ⟨p, hp⟩
    refine ⟨a • p, ?_⟩
    intro j hj
    simpa [response, mul_assoc, ← Finset.mul_sum] using congrArg (a * ·) (hp j hj)

/-- Number of independent consistent challenges on a fixed set. -/
noncomputable def fixedConsistencyDimension
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) (s : ℕ) : ℕ :=
  Module.finrank F (consistentChallenges (s := s) C W S)

/-- Exact fixed-set consistency count, directly from vector-space cardinality. -/
theorem fixedConsistent_card_eq_field_pow
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) :
    Nat.card {B : Challenge F m s // AgreesOn C W S B} =
      Nat.card F ^ fixedConsistencyDimension C W S s :=
  Module.natCard_eq_pow_finrank (K := F) (V := consistentChallenges C W S)

/-- The challenge dimension is its number of coefficients. -/
theorem finrank_challenge : Module.finrank F (Challenge F m s) = m * (s + 1) := by
  have hd : Module.finrank F (DegreeLT F (s + 1)) = s + 1 := by
    rw [(Polynomial.degreeLTEquiv F (s + 1)).finrank_eq, Module.finrank_fin_fun]
  simp [Challenge, Module.finrank_pi_fintype, hd]

/-- The number of independent linear conditions imposed by consistency. -/
noncomputable def fixedConsistencyCodimension
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) (s : ℕ) : ℕ :=
  m * (s + 1) - fixedConsistencyDimension C W S s

theorem fixedConsistencyDimension_add_codimension
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) :
    fixedConsistencyDimension C W S s + fixedConsistencyCodimension C W S s = m*(s+1) := by
  have h := Submodule.finrank_le (consistentChallenges (s := s) C W S)
  rw [finrank_challenge] at h
  exact Nat.add_sub_of_le h

/-- Exact challenge density, expressed using consistency codimension. -/
theorem fixedConsistent_density [Fintype F]
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n)) :
    (Nat.card {B : Challenge F m s // AgreesOn C W S B} : ℚ) /
      Nat.card (Challenge F m s) =
        1 / (Nat.card F : ℚ)^fixedConsistencyCodimension C W S s := by
  have hq : (Nat.card F : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [fixedConsistent_card_eq_field_pow,
    Module.natCard_eq_pow_finrank (K := F) (V := Challenge F m s), finrank_challenge]
  simp only [Nat.cast_pow]
  rw [← fixedConsistencyDimension_add_codimension C W S, pow_add]
  field_simp

/-- Exact density of an arbitrary challenge subspace. -/
theorem challengeSubspace_density [Fintype F] (K : Submodule F (Challenge F m s)) :
    (Nat.card K : ℚ) / Nat.card (Challenge F m s) =
      1 / (Nat.card F : ℚ)^(m*(s+1)-Module.finrank F K) := by
  have hq : (Nat.card F : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hle := K.finrank_le
  rw [finrank_challenge] at hle
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K),
    Module.natCard_eq_pow_finrank (K := F) (V := Challenge F m s), finrank_challenge]
  simp only [Nat.cast_pow]
  have he : m*(s+1) = Module.finrank F K + (m*(s+1)-Module.finrank F K) :=
    (Nat.add_sub_of_le hle).symm
  nth_rw 1 [he]
  rw [pow_add]
  field_simp

end RecursivePolygero.Local
