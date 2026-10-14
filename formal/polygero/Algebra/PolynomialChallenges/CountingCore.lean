import polygero.Algebra.PolynomialChallenges.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# Finite-field counting

Exact cardinality identities for finite challenge subspaces.
-/

namespace RecursivePolygero.Local

open Finset Function Polynomial
open Codes

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n R m s : ℕ}

/-- A finite-set presentation of a challenge subspace. -/
noncomputable def submoduleChallenges
    (K : Submodule F (Challenge F m s)) : Finset (Challenge F m s) := by
  classical
  exact Finset.univ.filter fun B ↦ B ∈ K

omit [DecidableEq F] in
@[simp] theorem mem_submoduleChallenges
    (K : Submodule F (Challenge F m s)) (B : Challenge F m s) :
    B ∈ submoduleChallenges K ↔ B ∈ K := by
  simp [submoduleChallenges]

omit [DecidableEq F] in
theorem card_submoduleChallenges
    (K : Submodule F (Challenge F m s)) :
    (submoduleChallenges K).card = Nat.card K := by
  classical
  simp [submoduleChallenges, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [Fintype F] [DecidableEq F] in
/-- Exact cardinality identity for a subspace, expressed using its
dimension gap. -/
theorem card_submodule_mul_field_pow_dimension_gap
    (K : Submodule F (Challenge F m s)) :
    Nat.card K * Nat.card F ^
        (Module.finrank F (Challenge F m s) - Module.finrank F K) =
      Nat.card (Challenge F m s) := by
  have hle : Module.finrank F K ≤ Module.finrank F (Challenge F m s) :=
    Submodule.finrank_le K
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K),
    Module.natCard_eq_pow_finrank (K := F) (V := Challenge F m s),
    ← pow_add]
  congr 1
  omega

omit [DecidableEq F] in
/-- A proper challenge subspace loses at least one field factor. -/
theorem card_submodule_mul_field_le
    (K : Submodule F (Challenge F m s)) (hK : K ≠ ⊤) :
    Nat.card K * Nat.card F ≤ Nat.card (Challenge F m s) := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K),
    Module.natCard_eq_pow_finrank (K := F) (V := Challenge F m s), ← pow_succ]
  exact pow_le_pow_right' Nat.card_pos (Submodule.finrank_lt hK)

end RecursivePolygero.Local
