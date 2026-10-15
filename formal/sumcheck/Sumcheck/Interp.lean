import Mathlib.LinearAlgebra.Lagrange

/-!
# Round polynomials, at any degree

A sumcheck prover sends one univariate polynomial per round, transmitted as its **evaluations**
at a fixed set of points rather than as coefficients.  This file is that object, for an arbitrary
degree `d`, together with the two facts every soundness and completeness argument downstream
rests on:

* a *disagreeing* round polynomial hits the true value at only `d` challenges
  (`univariate_roots_bound`) — the soundness direction;
* an *agreeing* one hits it at **every** challenge (`eval_lagrange_eq_of_agree`) — the
  completeness direction.

## Why `d` is a parameter

Implementations transmit a fixed number of evaluations, and the number differs by round *kind*.
Longfellow's `WPoly = Poly<3, Field>` is three evaluations, degree `2`, used by the ZK path; its
`CPoly = Poly<4, Field>` is four, degree `3`, used by the copy rounds of the non-ZK verifier.
Both are `RoundPoly F d` here — at `d = 2` and `d = 3` — and every theorem below applies to both,
so a development covering only one of them is not paying for the other.

## The interpolation points

`Interp F d` is the transmission format: which `d + 1` field elements the evaluations are taken
at.  Two of them are pinned, because the verifier's sum check reads exactly those:

* `pts 0 = 0` and `pts 1 = 1`, so `eval0 + eval1` is `p(0) + p(1)`.

The rest are free.  That matters for binary fields: Longfellow's third point is
`Field::poly_evaluation_point(2)`, which is `2` over a prime field but the generator `X` over
`GF(2)[X]/(Q(X))`, where `2 = 0` and `2` would not be a legal node.

`1 ≤ d` is not a field — it is *derived* (`Interp.one_le_degree`), since `d = 0` would force
`pts 0 = pts 1` and hence `0 = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Sumcheck

open Polynomial

/-- The `d + 1` distinct field elements a degree-`d` round polynomial is transmitted at, with
`0` and `1` in the first two slots because the sum check reads them. -/
class Interp (F : Type) [Field F] (d : ℕ) where
  pts : Fin (d + 1) → F
  pts_inj : Function.Injective pts
  pts_zero : pts 0 = 0
  pts_one : pts 1 = 1

namespace Interp

variable {F : Type} [Field F] {d : ℕ} [Interp F d]

/-- The nodes are distinct, in the form `Lagrange` wants it. -/
lemma pts_injOn :
    Set.InjOn (pts (F := F) (d := d)) ↑(Finset.univ : Finset (Fin (d + 1))) :=
  fun _ _ _ _ h => pts_inj h

/-- **A round polynomial has degree at least one.**  Not assumed: at `d = 0` the index type is a
subsingleton, so `pts 0 = pts 1` would give `(0 : F) = 1`.

`F` is explicit because the statement does not mention it, and Lean includes a section variable
only when it appears. -/
lemma one_le_degree (F : Type) [Field F] {d : ℕ} [Interp F d] : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · refine absurd ?_ (zero_ne_one (α := F))
    calc (0 : F) = pts (F := F) (0 : Fin 1) := pts_zero.symm
      _ = pts (F := F) (1 : Fin 1) := congrArg _ (Subsingleton.elim _ _)
      _ = 1 := pts_one
  · exact h

end Interp

/-- One round's transmitted polynomial: its values at the `d + 1` interpolation points. -/
structure RoundPoly (F : Type) (d : ℕ) where
  evals : Fin (d + 1) → F

namespace RoundPoly

variable {F : Type} [Field F] {d : ℕ} [Interp F d]

/-- The value at `0`; with `eval1`, one of the two the sum check reads. -/
abbrev eval0 (p : RoundPoly F d) : F := p.evals 0

/-- The value at `1`. -/
abbrev eval1 (p : RoundPoly F d) : F := p.evals 1

/-- The unique polynomial of degree `≤ d` through the transmitted points.  This is the object the
prover is committing to when it sends a round polynomial. -/
noncomputable def toPoly (p : RoundPoly F d) : Polynomial F :=
  Lagrange.interpolate Finset.univ (Interp.pts (F := F) (d := d)) p.evals

/-- Evaluation by Lagrange interpolation, as an implementation computes it — a weighted sum of the
transmitted values, with no polynomial ever formed.  `eval_toPoly` is that this is `toPoly`. -/
def eval_lagrange (p : RoundPoly F d) (r : F) : F :=
  ∑ i, p.evals i * ∏ j ∈ Finset.univ.erase i,
    (Interp.pts i - Interp.pts j)⁻¹ * (r - Interp.pts j)

@[simp] lemma eval_toPoly (p : RoundPoly F d) (r : F) :
    p.toPoly.eval r = p.eval_lagrange r := by
  simp [toPoly, eval_lagrange, Lagrange.interpolate_apply, Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.eval_finsetSum, Polynomial.eval_prod]

/-- The transmitted values are recovered at their own nodes. -/
@[simp] lemma eval_lagrange_pts (p : RoundPoly F d) (i : Fin (d + 1)) :
    p.eval_lagrange (Interp.pts i) = p.evals i := by
  rw [← eval_toPoly]
  exact Lagrange.eval_interpolate_at_node _ Interp.pts_injOn (Finset.mem_univ i)

@[simp] lemma eval_lagrange_zero (p : RoundPoly F d) : p.eval_lagrange 0 = p.eval0 := by
  rw [← Interp.pts_zero (F := F) (d := d), eval_lagrange_pts]

@[simp] lemma eval_lagrange_one (p : RoundPoly F d) : p.eval_lagrange 1 = p.eval1 := by
  rw [← Interp.pts_one (F := F) (d := d), eval_lagrange_pts]

/-- **The degree bound.**  `d + 1` evaluations determine a polynomial of degree at most `d`, and
this is what caps a cheating prover's luck at `d` challenges. -/
lemma toPoly_natDegree (p : RoundPoly F d) : p.toPoly.natDegree ≤ d := by
  by_cases hz : p.toPoly = 0
  · simp [hz]
  · have hlt : p.toPoly.degree < ((d + 1 : ℕ) : WithBot ℕ) := by
      have h := Lagrange.degree_interpolate_lt (v := Interp.pts (F := F) (d := d))
        p.evals Interp.pts_injOn
      simpa [toPoly] using h
    have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hlt
    omega

/--
**An agreeing round polynomial is the true one, everywhere.**

If the transmitted values match a degree-`≤ d` polynomial at all `d + 1` nodes, then
`eval_lagrange` reproduces that polynomial at *every* challenge — the difference has degree `≤ d`
and `d + 1` distinct roots.

This is the completeness converse of `univariate_roots_bound`, and it is what an honest prover
needs: agreement at the nodes is a finite check, agreement everywhere is what the verifier's
random challenge then tests for free.
-/
lemma eval_lagrange_eq_of_agree (p : RoundPoly F d) (P : Polynomial F)
    (hdeg : P.natDegree ≤ d) (hagree : ∀ i, p.evals i = P.eval (Interp.pts i)) (r : F) :
    p.eval_lagrange r = P.eval r := by
  have hPdeg : P.degree < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    by_cases hz : P = 0
    · simp [hz, Polynomial.degree_zero]
    · rw [Finset.card_univ, Fintype.card_fin]
      exact (Polynomial.natDegree_lt_iff_degree_lt hz).mp (by omega)
  have hkey : P = p.toPoly :=
    Lagrange.eq_interpolate_of_eval_eq _ Interp.pts_injOn hPdeg
      (fun i _ => (hagree i).symm)
  rw [← eval_toPoly, ← hkey]

/-- A round polynomial disagreeing with `P` at `0` or at `1` is a different polynomial. -/
lemma toPoly_sub_ne_zero (P : Polynomial F) (p : RoundPoly F d)
    (hdiff : p.eval0 ≠ P.eval 0 ∨ p.eval1 ≠ P.eval 1) :
    p.toPoly - P ≠ 0 := by
  intro hzero
  have heq : p.toPoly = P := sub_eq_zero.mp hzero
  have h0 : p.eval0 = P.eval 0 := by rw [← heq, eval_toPoly, eval_lagrange_zero]
  have h1 : p.eval1 = P.eval 1 := by rw [← heq, eval_toPoly, eval_lagrange_one]
  rcases hdiff with h | h
  · exact h h0
  · exact h h1

/--
**The cheating prover's luck is bounded by the degree.**

A prover that lies about the true round evaluations at `0` or `1` wins the round exactly when the
challenge is a root of `toPoly - P`, a non-zero polynomial of degree at most `max d e`.  Every
sumcheck soundness bound in the development is this lemma plus counting.
-/
lemma univariate_roots_bound (P : Polynomial F) (p : RoundPoly F d) (e : ℕ)
    (he : P.natDegree ≤ e) :
    p.eval0 ≠ P.eval 0 ∨ p.eval1 ≠ P.eval 1 →
    (p.toPoly - P).roots.card ≤ max d e := by
  intro _
  refine le_trans (Polynomial.card_roots' _) (le_trans (Polynomial.natDegree_sub_le _ _) ?_)
  exact max_le_max p.toPoly_natDegree he

end RoundPoly

end Sumcheck
