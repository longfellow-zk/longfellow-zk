import CodingTheory.ListDecoding.HahnDelsarte
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace CodingTheory.HahnDelsarte.Fast
open Finset Polynomial

def choose : ℕ → ℚ → ℚ
  | 0, _ => 1
  | k+1, x => (x-k)*choose k x/(k+1)

theorem choose_eq_pochhammer (k : ℕ) (x : ℚ) :
    choose k x = (descPochhammer ℚ k).eval x / (k.factorial : ℚ) := by
  induction k with
  | zero => simp [choose]
  | succ k ih =>
    rw [choose, ih, descPochhammer_succ_right, eval_mul, eval_sub, eval_X, eval_natCast, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_mul_eq_div_div]
    ring

theorem choose_nat (k n : ℕ) : choose k n = (n.choose k : ℚ) := by
  rw [choose_eq_pochhammer, Nat.cast_choose_eq_descPochhammer_div]

def kernel (n w k : ℕ) (x : ℚ) : ℚ :=
  ∑ i ∈ range (k+1), hahnWeight n w k i *
    ∑ a ∈ range (i+1), (choose a x * choose (i-a) (w-x)) *
      ∑ c ∈ range (k-i+1),
        (choose c (w-x)*choose (k-i-c) ((n:ℚ)+x-2*w))*hahnWeight n w k (a+c)

theorem kernel_nat (n w k t : ℕ) (ht : t ≤ w) (hn : 2*w ≤ n+t) :
    kernel n w k t = hahnKernel n w k t := by
  unfold kernel hahnKernel
  have hw : (w:ℚ)-(t:ℚ) = ((w-t:ℕ):ℚ) := (Nat.cast_sub ht).symm
  have hnt : (n:ℚ)+(t:ℚ)-2*w = ((n+t-2*w:ℕ):ℚ) := by
    rw [Nat.cast_sub hn, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp only [hw, hnt, choose_nat, Nat.cast_mul]

def polynomial (n w : ℕ) (coeffs : List ℕ) (x : ℚ) : ℚ :=
  (coeffs.headD 0 : ℚ) +
    ∑ k ∈ Icc 1 (coeffs.length-1), (coeffs.getD k 0 : ℚ)*kernel n w k x

theorem polynomial_nat (n w : ℕ) (coeffs : List ℕ) (t : ℕ)
    (ht : t ≤ w) (hn : 2*w ≤ n+t) :
    polynomial n w coeffs t = certificatePolynomial n w coeffs t := by
  simp only [polynomial, certificatePolynomial, kernel_nat n w _ t ht hn]

def eval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a::as, x => a+x*eval as x

/-- The compact polynomial check covers all realizable intersections exactly. -/
theorem certificate_of_polynomial (n w lam : ℕ) (cs : List ℕ) (p : List ℚ)
    (hw : lam ≤ w) (hn : 2*w ≤ n)
    (heq : ∀ x, polynomial n w cs x = eval p x)
    (hpos : 0 < cs.headD 0)
    (hneg : (List.range (lam+1)).all (fun t => decide (eval p t ≤ 0)) = true) :
    certificateValid n w lam cs = true := by
  simp only [certificateValid, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨hpos, fun t ht => Or.inr ?_⟩
  have h := (List.all_eq_true.mp hneg) t (List.mem_range.mpr ht)
  rw [decide_eq_true_eq] at h
  rw [← polynomial_nat n w cs t (by omega) (by omega), heq]
  exact h

theorem bound_of_polynomial (n w : ℕ) (cs : List ℕ) (p : List ℚ)
    (hn : 2*w ≤ n+w) (heq : ∀ x, polynomial n w cs x = eval p x) :
    certifiedBound n w cs = ⌊eval p w / (cs.headD 0 : ℚ)⌋₊ := by
  unfold certifiedBound
  rw [← polynomial_nat n w cs w le_rfl hn, heq]

end CodingTheory.HahnDelsarte.Fast
