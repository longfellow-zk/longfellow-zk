import polygero.Algebra.PolynomialChallenges.Consistency
import polygero.Algebra.PolynomialChallenges.CountingCore

/-! Restriction to arbitrary column sets and exact consistency counts. -/
namespace RecursivePolygero.Local
open Polynomial Finset Codes
variable {F : Type*} [Field F] {n R m d s : ℕ}

/-- Restricting to the selected columns preserves the consistency dimension. -/
theorem fixedConsistencyDimension_puncture
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n))
    (hRS : R ≤ S.card) :
    fixedConsistencyDimension C W S s =
      fixedConsistencyDimension (C.puncture S hRS)
        (fun i => C.restrictWord S (W i)) Finset.univ s := by
  have he : consistentChallenges (s := s) C W S =
      consistentChallenges (C.puncture S hRS)
        (fun i => C.restrictWord S (W i)) Finset.univ := by
    ext B
    exact agreesOn_iff_punctured_univ C W S hRS B
  unfold fixedConsistencyDimension
  rw [he]

/-- The number of polynomial challenges, in coefficient coordinates. -/
theorem card_challenge_eq_field_pow :
    Nat.card (Challenge F m s) = Nat.card F ^ (m * (s + 1)) := by
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_challenge]

section FiniteField
variable [Fintype F]

/-- A dimension deficit of at least `T+1` gives the fixed-core consistency penalty. -/
theorem fixedConsistent_card_mul_field_pow_le
    (C : RSCode F n R) (W : Fin m → Word F n) (S : Finset (Fin n))
    (T : ℕ)
    (hsmall : fixedConsistencyDimension C W S s + T + 1 ≤ m * (s + 1)) :
    Nat.card {B : Challenge F m s // AgreesOn C W S B} * Nat.card F ^ (T + 1) ≤
      Nat.card (Challenge F m s) := by
  rw [fixedConsistent_card_eq_field_pow, card_challenge_eq_field_pow, ← pow_add]
  exact pow_le_pow_right' (by exact Nat.card_pos) (by omega)

end FiniteField

end RecursivePolygero.Local
