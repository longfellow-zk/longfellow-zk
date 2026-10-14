import polygero.Algebra.PolynomialChallenges.Basic

namespace RecursivePolygero.Local
open Finset Function Polynomial Codes
variable {F : Type*} [Field F] [DecidableEq F]
variable {n R m d s D : Nat}

/-- Abstract pointwise and polynomial semantics for a secondary response.
No linearity is required; in a Ligero application `canonical` may include
quadratic arithmetic. -/
structure ResponseSemantics
    (C : RSCode F n R) (m d s D : Nat) where
  pointwise : Challenge F m s → Fin n → (Fin m → F) → F
  canonical : Challenge F m s → (Fin m → DegreeLT F d) → DegreeLT F D
  canonical_eval : ∀ B w z,
    ((canonical B w : DegreeLT F D) : F[X]).eval (C.node z) =
      pointwise B z (fun i => (w i : F[X]).eval (C.node z))

/-- The primary polynomial forced by a genuine degree-`< d` decoding. -/
noncomputable def canonicalPrimary
    (hR : R = d + s) (hd : 1 ≤ d)
    (B : Challenge F m s) (w : Fin m → DegreeLT F d) : DegreeLT F R := by
  let p : F[X] := ∑ i, (B i : F[X]) * (w i : F[X])
  refine ⟨p, ?_⟩
  apply Submodule.sum_mem
  intro i _hi
  have hmul := mul_mem_degreeLT_add_sub_one
    (show 1 ≤ s + 1 by omega) hd (B i).2 (w i).2
  simpa [hR, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul

omit [DecidableEq F] in
/-- Scalar normalization commutes with the canonical primary polynomial. -/
theorem canonicalPrimary_smul (hR : R = d+s) (hd : 1 ≤ d)
    (a : F) (B : Challenge F m s) (w : Fin m → DegreeLT F d) :
    canonicalPrimary hR hd (a • B) w = a • canonicalPrimary hR hd B w := by
  apply Subtype.ext
  simp only [canonicalPrimary, Pi.smul_apply, Submodule.coe_smul,
    Finset.smul_sum, Algebra.smul_mul_assoc]

omit [DecidableEq F] in
@[simp] theorem canonicalPrimary_eval
    (hR : R = d + s) (hd : 1 ≤ d)
    (B : Challenge F m s) (w : Fin m → DegreeLT F d) (z : Fin n)
    (C : RSCode F n R) :
    ((canonicalPrimary hR hd B w : DegreeLT F R) : F[X]).eval (C.node z) =
      ∑ i, (B i : F[X]).eval (C.node z) *
        (w i : F[X]).eval (C.node z) := by
  simp [canonicalPrimary, Polynomial.eval_finsetSum, Polynomial.eval_mul]


end RecursivePolygero.Local
