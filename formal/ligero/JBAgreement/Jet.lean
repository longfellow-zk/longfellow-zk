import Mathlib.Algebra.Polynomial.Identities
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# §1: stop the Hensel lift after `r + 1` coefficients

BCIKS construct the infinite Hensel series `γ = ∑_{t ≥ 0} α_t U^t` and devote their
Step 6 to proving `α_t = 0` for `t > r`.  That step is what drags the `X`-degree `D_X`
of the interpolant into the branch threshold, and it is the source of the extra factor
of `η`.

The finite-jet argument never forms the series.  It keeps only the `r`-jet

  `Γ_k(X) = ∑_{t = 0}^{r} α_t U^t`,   `U = X - x₀`,

and observes that this is already everything the affine-gluing argument needs.  The
justification is *finite Hensel uniqueness*, which this file proves in the two forms it
is used.

## Main results

* `eq_of_sub_isNilpotent_of_isUnit_derivative` — uniqueness of a root lifting a simple
  root modulo a nilpotent ideal.  Working modulo `U ^ (r+1)` makes `U` nilpotent, so
  this is exactly the statement that the truncated implicit-function recursion has a
  unique solution.  It holds over an arbitrary commutative ring, so no function field,
  valuation, or power series ring is required.

* `eq_of_sub_dvd_of_degree_le` — two polynomials of degree at most `r` that agree
  modulo `U ^ (r+1)` are equal.  This is the step "both sides have degree at most `r`,
  so `π_z(Γ_k) = p_z` as polynomials".

Together these give the conclusion of §1: the specialised jet *is* the proximate, with
no infinite series and no Step 6.
-/

namespace JBAgreement

open Polynomial

/-! ### Finite Hensel uniqueness -/

/-- **Uniqueness of a Hensel lift, finite form.**

If `y₁` and `y₂` are both roots of `f`, differ by a nilpotent, and `f'(y₁)` is a unit,
then `y₁ = y₂`.

Applied with the ambient ring `A[U] / (U ^ (r+1))` — in which `U` is nilpotent — this
says the truncated implicit-function recursion determines its solution uniquely.  The
hypothesis `IsUnit (f.derivative.eval y₁)` is the simple-root condition `ξ ≠ 0` of §1. -/
theorem eq_of_sub_isNilpotent_of_isUnit_derivative
    {B : Type*} [CommRing B] (f : B[X]) {y₁ y₂ : B}
    (h₁ : f.eval y₁ = 0) (h₂ : f.eval y₂ = 0)
    (hnil : IsNilpotent (y₂ - y₁))
    (hunit : IsUnit (f.derivative.eval y₁)) :
    y₂ = y₁ := by
  obtain ⟨c, hc⟩ := f.binomExpansion y₁ (y₂ - y₁)
  have hy : y₁ + (y₂ - y₁) = y₂ := by ring
  rw [hy, h₂, h₁] at hc
  -- `hc : 0 = 0 + f'(y₁) * (y₂ - y₁) + c * (y₂ - y₁) ^ 2`
  have hfac : (y₂ - y₁) * (f.derivative.eval y₁ + c * (y₂ - y₁)) = 0 := by
    linear_combination -hc
  have hnil' : IsNilpotent (c * (y₂ - y₁)) :=
    (Commute.all c (y₂ - y₁)).isNilpotent_mul_left hnil
  have hu : IsUnit (f.derivative.eval y₁ + c * (y₂ - y₁)) :=
    hnil'.isUnit_add_left_of_commute hunit (Commute.all _ _)
  have hzero : y₂ - y₁ = 0 := (hu.mul_left_eq_zero).mp hfac
  exact sub_eq_zero.mp hzero

/-! ### Degree truncation -/

/-- **Two `r`-jets that agree are equal.**

If `p` and `q` both have degree at most `r` and agree modulo `(X - x₀) ^ (r+1)`, they
are equal.  This is the second half of §1: the specialised jet `π_z(Γ_k)` and the
proximate `p_z` agree to order `r + 1` and both have degree at most `r`, hence coincide
as polynomials. -/
theorem eq_of_sub_dvd_of_degree_le {F : Type*} [Field F] {p q : F[X]} {r : ℕ} {x₀ : F}
    (hp : p.degree ≤ (r : ℕ)) (hq : q.degree ≤ (r : ℕ))
    (hdvd : (X - C x₀) ^ (r + 1) ∣ (p - q)) : p = q := by
  rw [← not_ne_iff]
  intro hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : ((X - C x₀) ^ (r + 1)).degree ≤ (p - q).degree :=
    degree_le_of_dvd hdvd hsub
  have hpow : ((X - C x₀) ^ (r + 1)).degree = ((r + 1 : ℕ) : WithBot ℕ) := by
    simp [degree_pow, degree_X_sub_C]
  have hle : (p - q).degree ≤ ((r : ℕ) : WithBot ℕ) :=
    le_trans (degree_sub_le p q) (max_le hp hq)
  rw [hpow] at hdeg
  have hfin : ((r + 1 : ℕ) : WithBot ℕ) ≤ ((r : ℕ) : WithBot ℕ) := le_trans hdeg hle
  rw [Nat.cast_le] at hfin
  omega

/-! ### Interpolation: pinning the jet down from `r + 1` coordinates

This is the last step of §3.  The incidence count produces `r + 1` coordinates on which
the jet `Γ_k` agrees with `v₀ + Z v₁`; both sides have `X`-degree at most `r`, so they
agree identically. -/

/-- Two polynomials of degree at most `r` agreeing at `r + 1` distinct points are equal. -/
theorem eq_of_eval_eq_of_degree_le {F : Type*} [Field F] [DecidableEq F] {p q : F[X]}
    {r : ℕ} (hp : p.degree ≤ (r : ℕ)) (hq : q.degree ≤ (r : ℕ))
    (T : Finset F) (hT : r + 1 ≤ T.card)
    (heval : ∀ x ∈ T, p.eval x = q.eval x) : p = q := by
  rw [← not_ne_iff]
  intro hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  -- `T` consists of roots of `p - q`.
  have hTroots : T ⊆ (p - q).roots.toFinset := by
    intro x hx
    have : (p - q).eval x = 0 := by
      simp [eval_sub, heval x hx]
    simpa [Multiset.mem_toFinset, mem_roots, hsub] using this
  have hnatdeg : (p - q).natDegree ≤ r := by
    have hle : (p - q).degree ≤ ((r : ℕ) : WithBot ℕ) :=
      le_trans (degree_sub_le p q) (max_le hp hq)
    exact natDegree_le_iff_degree_le.mpr hle
  have hcard : T.card ≤ r :=
    le_trans (le_trans (Finset.card_le_card hTroots) (p - q).roots.toFinset_card_le)
      (le_trans (card_roots' (p - q)) hnatdeg)
  omega

/-! ### The Newton step

Existence of the jet is a Newton iteration.  Because we only ever work modulo
`U ^ (r+1)`, the ideal is nilpotent and the iteration terminates after finitely many
steps — there is no completeness or power-series input.  This is the "finite recursion"
of §1, in the form that works in every characteristic. -/

/-- **One Newton step.**

If `f(a)` lies in an ideal `J` and `f'(a)` is invertible with inverse `u`, then the
Newton update `a - f(a) * u` stays in `a + J` and drives `f` into `J ^ 2`.

Iterating this is what produces the jet `Γ_k`; the quadratic gain `J → J ^ 2` is why
only finitely many steps are needed when `J` is nilpotent. -/
theorem eval_newton_mem_sq {B : Type*} [CommRing B] (f : B[X]) (a : B) (J : Ideal B)
    (hfa : f.eval a ∈ J) (u : B) (hu : f.derivative.eval a * u = 1) :
    f.eval (a - f.eval a * u) ∈ J ^ 2 ∧ (a - f.eval a * u) - a ∈ J := by
  have hdJ : -(f.eval a * u) ∈ J := neg_mem (Ideal.mul_mem_right _ _ hfa)
  have hda : a + -(f.eval a * u) = a - f.eval a * u := by ring
  obtain ⟨c, hc⟩ := f.binomExpansion a (-(f.eval a * u))
  have hcancel : f.derivative.eval a * -(f.eval a * u) = -f.eval a := by
    calc f.derivative.eval a * -(f.eval a * u)
        = -(f.eval a * (f.derivative.eval a * u)) := by ring
      _ = -(f.eval a * 1) := by rw [hu]
      _ = -f.eval a := by ring
  have hfd : f.eval (a - f.eval a * u) = c * (-(f.eval a * u)) ^ 2 := by
    rw [← hda, hc, hcancel]; ring
  refine ⟨?_, ?_⟩
  · rw [hfd]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hdJ 2)
  · have : (a - f.eval a * u) - a = -(f.eval a * u) := by ring
    rw [this]; exact hdJ

/-- **Existence of the jet: Hensel lifting over a nilpotent ideal.**

If `J ^ (2 ^ n) = ⊥`, `f(a) ∈ J`, and `f'(a)` is a unit, then `f` has a genuine root
congruent to `a` modulo `J`.

This is §1's finite recursion.  The proof is `2 ^ n`-fold Newton iteration: each step
squares the ideal, so nilpotency alone terminates it.  No completion, no formal power
series, and no restriction on the characteristic. -/
theorem exists_root_of_pow_eq_bot {B : Type*} [CommRing B] (f : B[X]) :
    ∀ (n : ℕ) (J : Ideal B), J ^ (2 ^ n) = ⊥ → ∀ a : B, f.eval a ∈ J →
      IsUnit (f.derivative.eval a) → ∃ b : B, f.eval b = 0 ∧ b - a ∈ J := by
  intro n
  induction n with
  | zero =>
      intro J hJ a hfa _
      refine ⟨a, ?_, by simp⟩
      have hJb : J = ⊥ := by simpa using hJ
      rw [hJb] at hfa
      simpa using hfa
  | succ n ih =>
      intro J hJ a hfa hunit
      obtain ⟨v, hv⟩ := hunit
      have hu : f.derivative.eval a * (↑v⁻¹ : B) = 1 := by
        rw [← hv]; exact v.mul_inv
      obtain ⟨hstep, hdiff⟩ := eval_newton_mem_sq f a J hfa (↑v⁻¹ : B) hu
      set a₁ := a - f.eval a * (↑v⁻¹ : B) with ha₁
      -- Every element of `J` is nilpotent.
      have hJnil : ∀ x ∈ J, IsNilpotent x := by
        intro x hx
        refine ⟨2 ^ (n + 1), ?_⟩
        have hmem := Ideal.pow_mem_pow hx (2 ^ (n + 1))
        rw [hJ] at hmem
        simpa using hmem
      -- The derivative stays invertible along the iteration.
      have hunit₁ : IsUnit (f.derivative.eval a₁) := by
        obtain ⟨c, hcc⟩ := sub_dvd_eval_sub a₁ a f.derivative
        have hmem : f.derivative.eval a₁ - f.derivative.eval a ∈ J := by
          rw [hcc]; exact Ideal.mul_mem_right _ _ hdiff
        have hnil : IsNilpotent (f.derivative.eval a₁ - f.derivative.eval a) := hJnil _ hmem
        have hres := hnil.isUnit_add_left_of_commute (hv ▸ v.isUnit) (Commute.all _ _)
        have heq : f.derivative.eval a + (f.derivative.eval a₁ - f.derivative.eval a)
            = f.derivative.eval a₁ := by ring
        rwa [heq] at hres
      -- Recurse with the squared ideal.
      have hJ2 : (J ^ 2) ^ (2 ^ n) = ⊥ := by
        rw [← pow_mul]
        have htwo : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
        rw [htwo]; exact hJ
      obtain ⟨b, hb0, hbd⟩ := ih (J ^ 2) hJ2 a₁ hstep hunit₁
      refine ⟨b, hb0, ?_⟩
      have hsplit : b - a = (b - a₁) + (a₁ - a) := by ring
      rw [hsplit]
      exact add_mem (Ideal.pow_le_self (by norm_num) hbd) hdiff

/-- The same statement for an arbitrary nilpotent ideal. -/
theorem exists_root_of_isNilpotent {B : Type*} [CommRing B] (f : B[X]) (J : Ideal B)
    {N : ℕ} (hJ : J ^ N = ⊥) (a : B) (hfa : f.eval a ∈ J)
    (hunit : IsUnit (f.derivative.eval a)) :
    ∃ b : B, f.eval b = 0 ∧ b - a ∈ J := by
  refine exists_root_of_pow_eq_bot f N J ?_ a hfa hunit
  have hle : N ≤ 2 ^ N := Nat.le_of_lt (Nat.lt_two_pow_self)
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ N = N + d := ⟨2 ^ N - N, by omega⟩
  rw [hd, pow_add, hJ]
  simp

end JBAgreement
