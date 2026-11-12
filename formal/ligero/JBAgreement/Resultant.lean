import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# §2: one quotient ring and one resultant lemma

BCIKS phrase the branch argument inside an algebraic function field `L / 𝔽_q(Z)`, and
need the theorem *an algebraic function with too many zeros is zero*.  The finite-jet
reorganisation replaces all of that by a single elementary statement about resultants,
proved here.

Write `F[Z][T]` for polynomials in `T` whose coefficients are polynomials in `Z`.  For
`z : F`, specialising `Z ↦ z` and evaluating `T ↦ t` is the ring hom
`eval₂ (evalRingHom z) t`.

## Main results

* `eval_resultant_eq_zero_of_common_root` — if `H(·, z)` and `g(·, z)` have a common
  root, then `Res_T(H, g)` vanishes at `z`.  Proved from the Bezout identity
  `H * p + g * q = C (Res(H,g))`, which holds over any commutative ring, so no degree
  bookkeeping under specialisation is needed.

* `card_badSpecializations_le` — consequently the *number* of such `z` is at most
  `deg_Z Res_T(H, g)`.  This is the whole zero-counting input of the branch argument:
  an ordinary polynomial root bound in place of a divisor-theoretic one.

The reduction "too many specialisations force divisibility by `H`" is then just the
contrapositive, `resultant_eq_zero_of_card_badSpecializations_gt`.
-/

namespace JBAgreement

open Polynomial

variable {F : Type*}

/-- Specialising `Z ↦ z` and evaluating `T ↦ t`, as a ring hom `F[Z][T] →+* F`. -/
noncomputable def spec [CommSemiring F] (z t : F) : F[X][X] →+* F :=
  eval₂RingHom (evalRingHom z) t

@[simp] lemma spec_apply [CommSemiring F] (z t : F) (f : F[X][X]) :
    spec z t f = eval₂ (evalRingHom z) t f := rfl

/-! ### The core specialisation lemma -/

/-- **§2, core.**  If the specialised polynomials `H(·, z)` and `g(·, z)` share a root
`t`, then the resultant `Res_T(H, g)`, an element of `F[Z]`, vanishes at `z`.

The proof evaluates the Bezout identity `H * p + g * q = C (Res(H, g))` under the ring
hom `spec z t`.  Because that identity holds over the *coefficient ring* `F[Z]`, there
is no need to control how degrees behave under specialisation. -/
theorem eval_resultant_eq_zero_of_common_root [CommRing F]
    (H g : F[X][X]) {m n : ℕ} (hH : H.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hmn : m ≠ 0 ∨ n ≠ 0) (z t : F)
    (hHz : eval₂ (evalRingHom z) t H = 0)
    (hgz : eval₂ (evalRingHom z) t g = 0) :
    eval z (resultant H g m n) = 0 := by
  obtain ⟨p, q, -, -, hbez⟩ := exists_mul_add_mul_eq_C_resultant H g hH hg hmn
  have hmap := congrArg (spec z t) hbez
  rw [map_add, map_mul, map_mul] at hmap
  simp only [spec_apply, hHz, hgz, zero_mul, add_zero, eval₂_C, coe_evalRingHom] at hmap
  exact hmap.symm

/-! ### Counting the bad specialisations -/

variable [Field F] [Fintype F] [DecidableEq F]

/-- The specialisations at which `H` and `g` acquire a common root. -/
noncomputable def badSpecializations (H g : F[X][X]) : Finset F :=
  Finset.univ.filter fun z => ∃ t : F,
    eval₂ (evalRingHom z) t H = 0 ∧ eval₂ (evalRingHom z) t g = 0

/-- **§2, the zero-counting lemma.**

If `Res_T(H, g) ≠ 0`, then the number of specialisations `z` at which `H(·, z)` and
`g(·, z)` acquire a common root is at most `deg_Z Res_T(H, g)`.

This single ordinary root bound replaces the algebraic-function-field zero theorem used
by BCIKS: places, valuations and divisors are not needed. -/
theorem card_badSpecializations_le (H g : F[X][X]) {m n : ℕ}
    (hH : H.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (hres : resultant H g m n ≠ 0) :
    (badSpecializations H g).card ≤ (resultant H g m n).natDegree := by
  set r := resultant H g m n with hr
  -- Every bad specialisation is a root of `r`.
  have hsub : badSpecializations H g ⊆ r.roots.toFinset := by
    intro z hz
    simp only [badSpecializations, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨t, hHz, hgz⟩ := hz
    have hroot : eval z r = 0 :=
      eval_resultant_eq_zero_of_common_root H g hH hg hmn z t hHz hgz
    simpa [Multiset.mem_toFinset, mem_roots, hres] using hroot
  calc (badSpecializations H g).card ≤ r.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card r.roots := r.roots.toFinset_card_le
    _ ≤ r.natDegree := card_roots' r

/-- The contrapositive actually used in the branch argument: too many specialisations
with a common root force the resultant to vanish identically, i.e. `H ∣ g` up to the
usual coprimality bookkeeping. -/
theorem resultant_eq_zero_of_card_badSpecializations_gt (H g : F[X][X]) {m n : ℕ}
    (hH : H.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (hcard : (resultant H g m n).natDegree < (badSpecializations H g).card) :
    resultant H g m n = 0 := by
  rw [← not_ne_iff]
  intro hres
  exact absurd (card_badSpecializations_le H g hH hg hmn hres) (not_le.mpr hcard)

/-! ### The height bound

To turn the zero count into the concrete branch bound `B` of §3 we need the `Z`-degree
of the resultant in terms of the `Z`-degrees of the coefficients of `H` and `g`.  This
is the "height" calculation of BCIKS Claim 5.10, and it is nothing more than reading off
the Sylvester determinant: the matrix has `m` columns carrying coefficients of `g` and
`n` columns carrying coefficients of `H`. -/

/-- **The height bound.**  If every coefficient of `H` has `Z`-degree at most `a` and
every coefficient of `g` has `Z`-degree at most `b`, then

`deg_Z Res_T(H, g) ≤ n * a + m * b`.

Each term of the Sylvester determinant is a product of `m + n` entries, `n` drawn from
`H`-columns and `m` from `g`-columns. -/
theorem natDegree_resultant_le {F : Type*} [CommRing F] (H g : F[X][X]) {a b : ℕ}
    (m n : ℕ) (hH : ∀ i, (H.coeff i).natDegree ≤ a)
    (hg : ∀ i, (g.coeff i).natDegree ≤ b) :
    (resultant H g m n).natDegree ≤ n * a + m * b := by
  rw [resultant, Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine le_trans (natDegree_smul_le _ _) (le_trans (natDegree_prod_le _ _) ?_)
  -- `m` columns of `g`-coefficients.
  have hleft : ∀ i : Fin m,
      (sylvester H g m n (σ (Fin.castAdd n i)) (Fin.castAdd n i)).natDegree ≤ b := by
    intro i
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs with h
    · exact hg _
    · simp
  -- `n` columns of `H`-coefficients.
  have hright : ∀ i : Fin n,
      (sylvester H g m n (σ (Fin.natAdd m i)) (Fin.natAdd m i)).natDegree ≤ a := by
    intro i
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs with h
    · exact hH _
    · simp
  calc ∑ i, (sylvester H g m n (σ i) i).natDegree
      = (∑ i : Fin m, (sylvester H g m n (σ (Fin.castAdd n i)) (Fin.castAdd n i)).natDegree)
        + ∑ i : Fin n, (sylvester H g m n (σ (Fin.natAdd m i)) (Fin.natAdd m i)).natDegree :=
        Fin.sum_univ_add _
    _ ≤ (∑ _i : Fin m, b) + ∑ _i : Fin n, a :=
        add_le_add (Finset.sum_le_sum fun i _ => hleft i) (Finset.sum_le_sum fun i _ => hright i)
    _ = m * b + n * a := by simp [Finset.sum_const, mul_comm]
    _ = n * a + m * b := by ring

end JBAgreement
