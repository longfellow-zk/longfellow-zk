import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The jet recursion, over a free variable

This file constructs the finite implicit-function jet of §1 and proves its defining
property.  Two design decisions remove machinery relative to both BCIKS and the plan:

1. **No field extension, no quotient ring.**  The recursion

     `α_t = -ξ⁻¹ · [Uᵗ] R(x₀ + U, Γ_{t-1}(U), Z)`

   never uses `R(x₀, α₀, Z) = 0`: the extraction of the diagonal term
   `∑_j R_{0j} · j · α₀^{j-1} · α_t = ξ · α_t` is an algebraic identity.  So the initial
   root `α₀` can be kept as a *free* symbol, the recursion run over any field `K`
   (downstream, `K = Frac(F[Z][T])` with `α₀ = T`), and the conclusion holds
   unconditionally:

     `R(x₀ + U, Γ_k(U), Z) ≡ R(x₀, α₀, Z)  (mod U^{r+1})`.

   Specialising `(Z, T) ↦ (z, t_z)` at a root `t_z` of the branch factor `H` kills the
   right-hand side *at the end*.  This meshes with the §2 machinery, whose
   `badSpecializations` already quantifies over pairs `(z, t)`.

2. **Hasse–Taylor updates.**  The step `Γ_t = Γ_{t-1} + α_t U^t` is analysed through
   `f(γ + δ) = ∑_ρ (D^ρ f)(γ) · δ^ρ` (Hasse derivatives, so valid in every
   characteristic), never through the multinomial expansion of the full composition.

Throughout, `R : K[X][X]` has the `U`-variable *inner* and the `Y`-variable *outer*;
`R.eval γ` for `γ : K[X]` is substitution of the jet into `Y`.

## Main results

* `jet` — the recursion; `jet R α₀ t` is the `t`-jet `Γ_t ∈ K[U]`.
* `coeff_eval_jet_eq_zero` — the vanishing `[Uˢ] R(Γ_t) = 0` for `1 ≤ s ≤ t`.
* `eval_jet_sub_C_dvd` — the packaged jet property
  `U^{r+1} ∣ R(Γ_k) - C (R(x₀, α₀))`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### The two structural constants

`xi` and `jetConst` make sense over any commutative ring; keeping them at that
generality is what lets the *same* names be used for the generic branch (over
`FractionRing (F[Z][T])`) and for each of its specialisations (over `F`), so that
specialising is a single naturality lemma rather than a re-derivation. -/

section Base

variable {B : Type*} [CommRing B]

/-- The simple-root value `ξ = (D¹_Y R)(x₀, α₀)`: evaluate the first Hasse derivative
of `R` at `U = 0`, `Y = α₀`.  (The recentering `X = x₀ + U` is assumed already
performed in `R`, so `U = 0` is the point `x₀`.) -/
noncomputable def xi (R : B[X][X]) (α₀ : B) : B :=
  ((hasseDeriv 1 R).map (evalRingHom 0)).eval α₀

/-- The obstruction constant `r₀ = R(x₀, α₀)`.  In the intended instantiation this is
`R(x₀, T, Z)`, killed later by specialising `T` to a root of the branch factor. -/
noncomputable def jetConst (R : B[X][X]) (α₀ : B) : B :=
  (R.map (evalRingHom 0)).eval α₀

end Base

variable {K : Type*} [Field K]

/-! ### The recursion -/

/-- The jet recursion: `Γ_0 = α₀` and
`Γ_{t+1} = Γ_t - ξ⁻¹ · ([U^{t+1}] R(Γ_t)) · U^{t+1}`. -/
noncomputable def jet (R : K[X][X]) (α₀ : K) : ℕ → K[X]
  | 0 => C α₀
  | t + 1 =>
      jet R α₀ t
        - C ((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) * X ^ (t + 1)

@[simp] theorem jet_zero (R : K[X][X]) (α₀ : K) : jet R α₀ 0 = C α₀ := rfl

theorem jet_succ (R : K[X][X]) (α₀ : K) (t : ℕ) :
    jet R α₀ (t + 1) =
      jet R α₀ t
        - C ((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1))) * X ^ (t + 1) := rfl

/-- The jet has degree at most its order. -/
theorem natDegree_jet_le (R : K[X][X]) (α₀ : K) : ∀ t, (jet R α₀ t).natDegree ≤ t
  | 0 => by simp
  | t + 1 => by
      rw [jet_succ]
      refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_jet_le R α₀ t) (by omega)
      · exact natDegree_C_mul_X_pow_le _ _

/-- The constant coefficient of every jet is the initial value `α₀`. -/
theorem jet_coeff_zero (R : K[X][X]) (α₀ : K) : ∀ t, (jet R α₀ t).coeff 0 = α₀
  | 0 => by simp
  | t + 1 => by
      rw [jet_succ, coeff_sub, coeff_mul_X_pow']
      simp [jet_coeff_zero R α₀ t]

/-! ### Hasse–Taylor expansion of an evaluation -/

/-- Taylor expansion of `f.eval (γ + δ)` in the increment `δ`, with Hasse-derivative
coefficients.  Valid over any commutative ring; this is the only expansion tool the
whole jet analysis uses. -/
theorem eval_add_eq_sum_hasseDeriv {S : Type*} [CommRing S] (f : S[X]) (γ δ : S) :
    f.eval (γ + δ) = ∑ ρ ∈ range (f.natDegree + 1), (hasseDeriv ρ f).eval γ * δ ^ ρ := by
  have h1 : f.eval (γ + δ) = f.eval (δ + γ) := by rw [add_comm]
  rw [h1, ← taylor_eval]
  rw [eval_eq_sum_range' (n := f.natDegree + 1) (by rw [natDegree_taylor]; omega)]
  exact Finset.sum_congr rfl fun ρ _ => by rw [taylor_coeff]

/-! ### Constant coefficients of evaluations -/

/-- Extracting the constant `U`-coefficient of `S.eval γ` only sees the constant
coefficients: it equals the `U = 0` slice of `S` evaluated at `γ(0)`. -/
theorem coeff_zero_eval {B : Type*} [CommRing B] (S : B[X][X]) (γ : B[X]) :
    (S.eval γ).coeff 0 = (S.map (evalRingHom 0)).eval (γ.coeff 0) := by
  induction S using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      rw [eval_monomial, map_monomial, eval_monomial]
      rw [coeff_zero_eq_eval_zero, eval_mul, eval_pow]
      rw [coeff_zero_eq_eval_zero]
      simp

/-- The `ξ`-transport: at every stage of the recursion, the constant coefficient of the
first Hasse derivative evaluated at the jet is still `ξ`. -/
theorem coeff_zero_hasseDeriv_eval_jet (R : K[X][X]) (α₀ : K) (t : ℕ) :
    ((hasseDeriv 1 R).eval (jet R α₀ t)).coeff 0 = xi R α₀ := by
  rw [coeff_zero_eval, jet_coeff_zero, xi]

/-! ### The update analysis -/

/-- The Taylor form of one recursion step. -/
theorem eval_jet_succ (R : K[X][X]) (α₀ : K) (t : ℕ) :
    R.eval (jet R α₀ (t + 1)) =
      ∑ ρ ∈ range (R.natDegree + 1),
        (hasseDeriv ρ R).eval (jet R α₀ t) *
          (C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) * X ^ (t + 1)) ^ ρ := by
  have h : jet R α₀ (t + 1) =
      jet R α₀ t +
        C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) * X ^ (t + 1) := by
    rw [jet_succ, map_neg]
    ring
  rw [h, eval_add_eq_sum_hasseDeriv]

/-- Coefficients strictly below the update order are unchanged by one recursion step. -/
theorem coeff_eval_jet_succ_of_le (R : K[X][X]) (α₀ : K) {s t : ℕ} (hs : s ≤ t) :
    (R.eval (jet R α₀ (t + 1))).coeff s = (R.eval (jet R α₀ t)).coeff s := by
  rw [eval_jet_succ, finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro ρ _ hρ
    have hpow : (C (-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) *
        X ^ (t + 1)) ^ ρ =
        C ((-((xi R α₀)⁻¹ * ((R.eval (jet R α₀ t)).coeff (t + 1)))) ^ ρ) *
          X ^ ((t + 1) * ρ) := by
      rw [mul_pow, ← C_pow, ← pow_mul]
    rw [hpow, ← mul_assoc, coeff_mul_X_pow']
    have : ¬ (t + 1) * ρ ≤ s := by
      have hρ1 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.mpr hρ
      nlinarith
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- **The cancellation.**  At the update order itself, the `ρ = 1` Taylor term
contributes `ξ · (-ξ⁻¹ · b)` against the old coefficient `b`, so the new coefficient
vanishes.  This needs `ξ ≠ 0` and nothing else. -/
theorem coeff_eval_jet_succ_self (R : K[X][X]) (α₀ : K) (t : ℕ) (hξ : xi R α₀ ≠ 0) :
    (R.eval (jet R α₀ (t + 1))).coeff (t + 1) = 0 := by
  -- `R` is not constant in `Y`: otherwise `ξ = 0`.
  have hdeg : 1 ≤ R.natDegree := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro h0
    have hC : R = C (R.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have : xi R α₀ = 0 := by
      rw [xi, hC, hasseDeriv_C _ _ (by norm_num)]
      simp
    exact hξ this
  set b := (R.eval (jet R α₀ t)).coeff (t + 1) with hb
  set c := -((xi R α₀)⁻¹ * b) with hc
  rw [eval_jet_succ, finsetSum_coeff]
  -- Only `ρ = 0` and `ρ = 1` survive at coefficient `t + 1`.
  have hsub : ({0, 1} : Finset ℕ) ⊆ range (R.natDegree + 1) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
  have hzero : ∀ ρ ∈ range (R.natDegree + 1), ρ ∉ ({0, 1} : Finset ℕ) →
      ((hasseDeriv ρ R).eval (jet R α₀ t) *
        (C c * X ^ (t + 1)) ^ ρ).coeff (t + 1) = 0 := by
    intro ρ _ hρnot
    have hρ2 : 2 ≤ ρ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hρnot
      omega
    have hpow : (C c * X ^ (t + 1)) ^ ρ = C (c ^ ρ) * X ^ ((t + 1) * ρ) := by
      rw [mul_pow, ← C_pow, ← pow_mul]
    rw [hpow, ← mul_assoc, coeff_mul_X_pow']
    have : ¬ (t + 1) * ρ ≤ t + 1 := by nlinarith
    simp [this]
  rw [← Finset.sum_subset hsub hzero]
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  -- The `ρ = 0` term: the old coefficient `b`.
  have h0 : ((hasseDeriv 0 R).eval (jet R α₀ t) *
      (C c * X ^ (t + 1)) ^ 0).coeff (t + 1) = b := by
    rw [pow_zero, mul_one, hasseDeriv_zero']
  -- The `ρ = 1` term: `ξ · c = -b`.
  have h1 : ((hasseDeriv 1 R).eval (jet R α₀ t) *
      (C c * X ^ (t + 1)) ^ 1).coeff (t + 1) = xi R α₀ * c := by
    rw [pow_one, ← mul_assoc, coeff_mul_X_pow']
    simp only [le_refl, if_true, Nat.sub_self]
    rw [coeff_mul_C, coeff_zero_hasseDeriv_eval_jet]
  rw [h0, h1, hc]
  field_simp
  ring

/-! ### The vanishing theorem and the jet property -/

/-- **The vanishing.**  All `U`-coefficients of `R(Γ_t)` in orders `1, …, t` are zero:
the `t`-jet solves the equation to order `t`. -/
theorem coeff_eval_jet_eq_zero (R : K[X][X]) (α₀ : K) (hξ : xi R α₀ ≠ 0) :
    ∀ t, ∀ s, 1 ≤ s → s ≤ t → (R.eval (jet R α₀ t)).coeff s = 0 := by
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
      intro s hs1 hst
      rcases Nat.lt_or_ge s (t + 1) with hlt | hge
      · rw [coeff_eval_jet_succ_of_le R α₀ (by omega)]
        exact ih s hs1 (by omega)
      · have : s = t + 1 := by omega
        rw [this]
        exact coeff_eval_jet_succ_self R α₀ t hξ

/-- The constant coefficient of `R(Γ_t)` is the obstruction `r₀ = R(x₀, α₀)`,
independently of `t`. -/
theorem coeff_zero_eval_jet (R : K[X][X]) (α₀ : K) (t : ℕ) :
    (R.eval (jet R α₀ t)).coeff 0 = jetConst R α₀ := by
  rw [coeff_zero_eval, jet_coeff_zero, jetConst]

/-- **The jet property (§1, conclusion).**

`U^{r+1}` divides `R(Γ_k) - r₀`.  In the intended instantiation `r₀ = R(x₀, T, Z)`
specialises to `0` at every branch point `(z, t_z)`, making the specialised jet a root
of `R(x₀+U, ·, z)` modulo `U^{r+1}`; finite Hensel uniqueness (`Jet.lean`) then
identifies it with the proximate `p_z`. -/
theorem eval_jet_sub_C_dvd (R : K[X][X]) (α₀ : K) (hξ : xi R α₀ ≠ 0) (r : ℕ) :
    (X : K[X]) ^ (r + 1) ∣ R.eval (jet R α₀ r) - C (jetConst R α₀) := by
  rw [X_pow_dvd_iff]
  intro d hd
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · rw [coeff_sub, coeff_zero_eval_jet, coeff_C]
    simp
  · rw [coeff_sub, coeff_eval_jet_eq_zero R α₀ hξ r d hdpos (by omega), coeff_C]
    simp
    omega

end JBAgreement
