import polygero.Algebra.PolynomialChallenges.SelectedColumns
import polygero.Algebra.PolynomialChallenges.DegreeLowering
import Mathlib.LinearAlgebra.Lagrange

/-! Full consistency determines fixed lower-degree row polynomials by ordinary
polynomial identities. No retained-set or proximity-gap argument is used. -/
namespace RecursivePolygero.Local
open Finset Polynomial Codes
variable {F : Type*} [Field F] {n k m s : ℕ}

/-- Full consistency on more than the response degree bound forces all rows
to have the lower degree bound. Consecutive monomial challenges prevent wraparound. -/
theorem rows_of_full_consistency (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (T : Finset (Fin n)) (hk : 1 ≤ k) (hsize : k+s < T.card)
    (hall : consistentChallenges (s := s) C W T = ⊤) :
    ∃ f : Fin m → DegreeLT F k,
      ∀ i j, j ∈ T → W i j = (f i : F[X]).eval (C.node j) := by
  classical
  let mon (a : Fin (s+1)) : DegreeLT F (s+1) :=
    ⟨X^a.val,mem_degreeLT.mpr (by rw [degree_X_pow]; exact_mod_cast a.isLt)⟩
  have hex (i : Fin m) (a : Fin (s+1)) : ∃ p : DegreeLT F (k+s),
      ∀ j ∈ T, C.node j ^ a.val * W i j = (p : F[X]).eval (C.node j) := by
    have hmem : Pi.single i (mon a) ∈ consistentChallenges (s := s) C W T := by
      rw [hall]; exact Submodule.mem_top
    obtain ⟨p,hp⟩ := hmem
    refine ⟨p,?_⟩
    intro j hj
    simpa [response, Pi.single_apply, mon, apply_ite] using hp j hj
  choose p hp using hex
  have hstep (i : Fin m) (a : ℕ) (ha : a < s) :
      X * (p i ⟨a,by omega⟩ : F[X]) = (p i ⟨a+1,by omega⟩ : F[X]) := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq T C.node_injective.injOn
    · have hd := mul_mem_degreeLT_add_sub_one (by omega : 1 ≤ 2)
        (by omega : 1 ≤ k+s) (show (X : F[X]) ∈ degreeLT F 2 by
          rw [mem_degreeLT, degree_X]; norm_cast)
        (p i ⟨a,by omega⟩).2
      exact (mem_degreeLT.mp hd).trans_le (by exact_mod_cast (by omega : 2+(k+s)-1 ≤ T.card))
    · exact (mem_degreeLT.mp (p i ⟨a+1,by omega⟩).2).trans_le
        (by exact_mod_cast hsize.le)
    · intro j hj
      rw [eval_mul, eval_X, ← hp i ⟨a,by omega⟩ j hj, ← hp i ⟨a+1,by omega⟩ j hj]
      simp only [pow_succ']
      ring
  have hpow (i : Fin m) (a : ℕ) (ha : a ≤ s) :
      (p i ⟨a,by omega⟩ : F[X]) = X^a * (p i ⟨0,by omega⟩ : F[X]) := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [← hstep i a (by omega), ih (by omega), pow_succ']
      ring
  have hdegree (i : Fin m) : (p i ⟨0,by omega⟩ : F[X]) ∈ degreeLT F k := by
    apply mem_degreeLT_of_X_pow_mul_mem_degreeLT (s := s)
    rw [← hpow i s le_rfl]
    exact (p i ⟨s,by omega⟩).2
  refine ⟨fun i => ⟨p i ⟨0,by omega⟩,hdegree i⟩,?_⟩
  intro i j hj
  simpa using hp i ⟨0,by omega⟩ j hj

end RecursivePolygero.Local
