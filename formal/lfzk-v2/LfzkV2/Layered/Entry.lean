import LfzkV2.Native.Circuit
import LfzkV2.Challenges

/-!
# Entering zero-output checks at a layer boundary

An entry remaps the existing weights into the next global output array and
adds independent weights on newly entering zero outputs. It owns no wire
array. The optional carry map accounts for the implicit zero padding beyond
an actual width; the fresh map may overlap the carry map at the shared input
boundary. Neither injectivity nor disjointness is needed for the algebra.
-/

namespace LfzkV2.Layered

open SumcheckV2 Finset
open scoped Classical

variable {F Old New : Type} [Field F] [Fintype Old] [Fintype New]

structure Entry (Old New : Type) (checks : ℕ) where
  carry : Old → Option New
  fresh : Fin checks → New

namespace Entry

variable {checks : ℕ} (e : Entry Old New checks)

noncomputable def previous (w : New → F) : Old → F :=
  fun i => (e.carry i).elim 0 w

def residuals (w : New → F) : Fin checks → F := w ∘ e.fresh

noncomputable def weights (a : Old → F) (rho : Fin checks → F) : New → F :=
  fun j => (∑ i, if e.carry i = some j then a i else 0) +
    ∑ i, if e.fresh i = j then rho i else 0

theorem dot_weights (a : Old → F) (rho : Fin checks → F) (w : New → F) :
    dot (e.weights a rho) w = dot a (e.previous w) + dot rho (e.residuals w) := by
  simp only [dot, weights, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    cases h : e.carry i with
    | none => simp [previous, h]
    | some j => simp [previous, h]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [residuals]

/-- If all new outputs vanish, entering them preserves the current claim. -/
theorem dot_weights_of_zero (a : Old → F) (rho : Fin checks → F) (w : New → F)
    (hzero : ∀ i, e.residuals w i = 0) :
    dot (e.weights a rho) w = dot a (e.previous w) := by
  rw [e.dot_weights]
  simp [dot, hzero]

/-- A false newly entering output can be hidden only by the same prefix-local
linear cancellation event used for independent assertion coefficients. -/
theorem cancellation (a : Old → F) (rho : Fin checks → F) (w : New → F) (claim : F)
    (hfalse : ∃ i, e.residuals w i ≠ 0)
    (hclaim : claim = dot (e.weights a rho) w) :
    AssertionBad (dot a (e.previous w)) claim rho (e.residuals w) := by
  apply assertion_reduction _ _ _ _ hfalse
  exact hclaim.trans (e.dot_weights a rho w)

end Entry
end LfzkV2.Layered
