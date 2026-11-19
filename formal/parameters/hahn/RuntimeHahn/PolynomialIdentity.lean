import RuntimeHahn.HahnPolynomial
import Mathlib.Algebra.Polynomial.Roots

/-! Polynomial degree bounds used to check Hahn identities at finitely many points. -/

namespace CodingTheory.HahnDelsarte.Fast.Identity
open Polynomial Finset

noncomputable def choosePoly : ℕ → ℚ → ℚ → Polynomial ℚ
  | 0, _, _ => 1
  | k + 1, a, b =>
    C (1 / (k + 1 : ℚ)) * ((C (a - k) + X * C b) * choosePoly k a b)

theorem eval_choosePoly (k : ℕ) (a b x : ℚ) :
    (choosePoly k a b).eval x = choose k (a + b * x) := by
  induction k with
  | zero => simp [choosePoly, choose]
  | succ k ih => simp only [choosePoly, eval_mul, eval_C, eval_add, eval_X, ih, choose]; ring

theorem degree_choosePoly (k : ℕ) (a b : ℚ) : (choosePoly k a b).natDegree ≤ k := by
  induction k with
  | zero => simp [choosePoly]
  | succ k ih =>
    apply le_trans (natDegree_C_mul_le _ _) (le_trans natDegree_mul_le ?_)
    have h : (C (a - k) + X * C b : Polynomial ℚ).natDegree ≤ 1 :=
      natDegree_add_le_of_degree_le (by rw [natDegree_C]; omega)
        (le_trans (natDegree_mul_C_le _ _) (by simp))
    omega

noncomputable def kernelPoly (n w k : ℕ) : Polynomial ℚ :=
  ∑ i ∈ range (k + 1), C (hahnWeight n w k i) *
    ∑ a ∈ range (i + 1), (choosePoly a 0 1 * choosePoly (i - a) w (-1)) *
      ∑ c ∈ range (k - i + 1),
        (choosePoly c w (-1) * choosePoly (k - i - c) ((n : ℚ) - 2 * w) 1) *
          C (hahnWeight n w k (a + c))

theorem eval_kernelPoly (n w k : ℕ) (x : ℚ) :
    (kernelPoly n w k).eval x = Fast.kernel n w k x := by
  simp only [kernelPoly, eval_finsetSum, eval_mul, eval_C, eval_choosePoly, Fast.kernel,
    one_mul, zero_add, neg_one_mul, ← sub_eq_add_neg]
  congr 1
  funext i
  congr 1
  apply sum_congr rfl
  intro a _
  congr 1
  apply sum_congr rfl
  intro c _
  rw [show (n : ℚ) - 2 * w + x = n + x - 2 * w by ring]

theorem degree_kernelPoly (n w k : ℕ) : (kernelPoly n w k).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have hi' : i ≤ k := by simpa using mem_range.mp hi
  apply le_trans (natDegree_C_mul_le _ _)
  apply natDegree_sum_le_of_forall_le
  intro a ha
  have ha' : a ≤ i := by simpa using mem_range.mp ha
  have hleft : (choosePoly a 0 1 * choosePoly (i - a) w (-1)).natDegree ≤ i := by
    have h := natDegree_mul_le (p := choosePoly a 0 1) (q := choosePoly (i - a) w (-1))
    have h₁ := degree_choosePoly a 0 1
    have h₂ := degree_choosePoly (i - a) w (-1)
    omega
  have hright : (∑ c ∈ range (k - i + 1),
      (choosePoly c w (-1) * choosePoly (k - i - c) ((n : ℚ) - 2 * w) 1) *
        C (hahnWeight n w k (a + c))).natDegree ≤ k - i := by
    apply natDegree_sum_le_of_forall_le
    intro c hc
    have hc' : c ≤ k - i := by simpa using mem_range.mp hc
    apply le_trans (natDegree_mul_C_le _ _) (le_trans natDegree_mul_le ?_)
    have h₁ := degree_choosePoly c w (-1)
    have h₂ := degree_choosePoly (k - i - c) ((n : ℚ) - 2 * w) 1
    omega
  exact le_trans natDegree_mul_le (by omega)

noncomputable def ofList : List ℤ → Polynomial ℚ
  | [] => 0
  | a :: p => C (a : ℚ) + X * ofList p

theorem degree_ofList (p : List ℤ) : (ofList p).natDegree ≤ p.length - 1 := by
  induction p with
  | nil => simp [ofList]
  | cons a p ih =>
    cases p with
    | nil => simp [ofList]
    | cons b p =>
      apply natDegree_add_le_of_degree_le (by simp)
      apply le_trans natDegree_mul_le
      simp only [natDegree_X, List.length_cons] at *
      omega

theorem eval_div (p : List ℤ) (d x : ℚ) :
    Fast.eval (p.map fun a : ℤ => (a : ℚ) / d) x = (ofList p).eval x / d := by
  induction p with
  | nil => simp [ofList, Fast.eval]
  | cons a p ih => simp only [List.map_cons, Fast.eval, ih, ofList, eval_add, eval_C, eval_mul, eval_X]; ring

theorem kernel_eq_of_values (n w k : ℕ) (p : List ℤ) (d : ℕ)
    (hlen : p.length ≤ k + 1) (hk : k ≤ w)
    (h : ∀ t ≤ k, Fast.kernel n w k (w - t : ℕ) =
      (ofList p).eval ((w - t : ℕ) : ℚ) / d) (x : ℚ) :
    Fast.kernel n w k x = Fast.eval (p.map fun a : ℤ => (a : ℚ) / d) x := by
  have heq : kernelPoly n w k = C (1 / (d : ℚ)) * ofList p := by
    apply eq_of_natDegree_lt_card_of_eval_eq (f := fun t : Fin (k + 1) => ((w - t.val : ℕ) : ℚ))
    · intro a b hab
      dsimp only at hab
      have hab' : w - a.val = w - b.val := by exact_mod_cast hab
      apply Fin.ext
      have := a.isLt
      have := b.isLt
      omega
    · intro t
      rw [eval_kernelPoly, h t.val (by omega), eval_mul, eval_C]
      ring
    · have h₁ := degree_kernelPoly n w k
      have h₂ := (natDegree_C_mul_le (1 / (d : ℚ)) (ofList p)).trans (degree_ofList p)
      simp only [Fintype.card_fin]
      omega
  rw [← eval_kernelPoly, heq, eval_mul, eval_C, eval_div]
  ring

end CodingTheory.HahnDelsarte.Fast.Identity
