import polygero.Algebra.PolynomialChallenges.Consistency
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

namespace RecursivePolygero.Local.Shift
open Polynomial Finset Submodule RecursivePolygero.Local
variable {F : Type*} [Field F] {n : ℕ}

noncomputable def evaluate (x : Fin n → F) : F[X] →ₗ[F] (Fin n → F) where
  toFun p j := p.eval (x j)
  map_add' := by intros; ext; simp
  map_smul' := by intros; ext; simp

noncomputable def shift (x : Fin n → F) : Module.End F (Fin n → F) where
  toFun w j := x j * w j
  map_add' := by intros; ext; simp [mul_add]
  map_smul' := by intros; ext; simp [mul_left_comm]

noncomputable def evalSpace (x : Fin n → F) (a : ℕ) : Submodule F (Fin n → F) :=
  (degreeLT F a).map (evaluate x)

theorem evalSpace_mono (x : Fin n → F) : Monotone (evalSpace x) :=
  fun _ _ h => Submodule.map_mono (degreeLT_mono h)

theorem shift_evaluate (x : Fin n → F) (p : F[X]) :
    shift x (evaluate x p) = evaluate x (X*p) := by ext; simp [shift,evaluate]

theorem shift_pow_apply (x : Fin n → F) (j : ℕ) (w : Fin n → F) (i : Fin n) :
    ((shift x)^j) w i = x i ^ j * w i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    change x i * ((shift x)^j) w i = _
    rw [ih, pow_succ']
    exact (mul_assoc ..).symm

/-- Pointwise multiplication by an ordinary scalar polynomial. -/
noncomputable def multiplyWord (x : Fin n → F) (p : F[X]) (w : Fin n → F) : Fin n → F :=
  fun i => p.eval (x i) * w i

theorem evaluate_injective (x : Fin n → F) (hx : Function.Injective x)
    {a : ℕ} (ha : a ≤ n) : Function.Injective ((evaluate x).comp (degreeLT F a).subtype) := by
  intro p q he
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hx.injOn
  · simpa using (mem_degreeLT.mp p.2).trans_le (by exact_mod_cast ha)
  · simpa using (mem_degreeLT.mp q.2).trans_le (by exact_mod_cast ha)
  · intro j _; exact congrFun he j

theorem finrank_evalSpace (x : Fin n → F) (hx : Function.Injective x)
    {a : ℕ} (ha : a ≤ n) : Module.finrank F (evalSpace x a) = a := by
  have hr : LinearMap.range ((evaluate x).comp (degreeLT F a).subtype) = evalSpace x a := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [← hr, LinearMap.finrank_range_of_inj (evaluate_injective x hx ha)]
  exact (Polynomial.degreeLTEquiv F a).finrank_eq.trans (Module.finrank_fin_fun F)

theorem evalSpace_top (x : Fin n → F) (hx : Function.Injective x) : evalSpace x n = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa using finrank_evalSpace x hx le_rfl

theorem evalSpace_le_iff (x : Fin n → F) (a : ℕ) (U : Submodule F (Fin n → F)) :
    evalSpace x a ≤ U ↔ ∀ j < a, evaluate x (X^j) ∈ U := by
  constructor
  · intro h j hj
    apply h
    exact ⟨X^j, mem_degreeLT.mpr (by simpa using hj), rfl⟩
  · intro h w hw
    obtain ⟨p,hp,rfl⟩ := hw
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum, map_sum]
    apply U.sum_mem
    intro j hj
    rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul, map_smul]
    apply U.smul_mem
    apply h
    have hc := (Polynomial.degree_lt_iff_coeff_zero _ _).mp (mem_degreeLT.mp hp)
    by_contra hn
    exact (Polynomial.mem_support_iff.mp hj) (hc j (by omega))

end RecursivePolygero.Local.Shift
