import LfzkV2.PolygeroMasking

/-!
# Polygero's additive primary mask

The primary response is `sum_i B_i * W_i + fstar`. Each ordinary row has
degree below `k`; the challenge polynomials have degree at most `s`, so the
response and its uniformly sampled additive mask have degree below `k+s`.
Changing the ordinary rows while preserving their openings can be absorbed
by a translation of `fstar` that preserves its openings as well.
-/

namespace LfzkV2.PolygeroPrimaryMasking

open Polynomial Finset LigeroFamily MultiplicativeCode
open RecursivePolygero.Local

variable {F : Type} [Field F] {k s m n t : ℕ}

noncomputable def batch (hk : 0 < k) (B : Challenge F m s)
    (rows : Fin m → DegreeLT F k) : DegreeLT F (k+s) :=
  ⟨∑ i, (B i : F[X]) * (rows i : F[X]), by
    apply Submodule.sum_mem
    intro i _
    have hp := mul_mem_degreeLT_add_sub_one (Nat.succ_le_succ (Nat.zero_le s))
      hk (B i).2 (rows i).2
    convert! hp using 1; congr 1; omega⟩

theorem batch_eval (hk : 0 < k) (B : Challenge F m s) (rows : Fin m → DegreeLT F k) (x : F) :
    (batch hk B rows : F[X]).eval x = ∑ i, (B i : F[X]).eval x * (rows i : F[X]).eval x := by
  simp [batch, Polynomial.eval_finsetSum]

noncomputable def response (hk : 0 < k) (B : Challenge F m s)
    (rows : Fin m → DegreeLT F k) (mask : DegreeLT F (k+s)) : DegreeLT F (k+s) :=
  batch hk B rows + mask

noncomputable def translate (hk : 0 < k) (B : Challenge F m s)
    (source target : Fin m → DegreeLT F k) : DegreeLT F (k+s) ≃ DegreeLT F (k+s) :=
  Equiv.addRight (batch hk B source - batch hk B target)

theorem translate_response (hk : 0 < k) (B : Challenge F m s)
    (source target : Fin m → DegreeLT F k) (mask : DegreeLT F (k+s)) :
    response hk B target (translate hk B source target mask) = response hk B source mask := by
  change batch hk B target + (mask + (batch hk B source - batch hk B target)) = _
  unfold response
  abel

theorem translate_openings (hk : 0 < k) (B : Challenge F m s)
    (source target : Fin m → DegreeLT F k) (mask : DegreeLT F (k+s))
    (nodes : Fin n → F) (Q : QuerySet n t)
    (hquery : ∀ i (j : ↥Q.coordinates),
      (source i : F[X]).eval (nodes j.1) = (target i : F[X]).eval (nodes j.1))
    (j : ↥Q.coordinates) :
    (translate hk B source target mask : F[X]).eval (nodes j.1) =
      (mask : F[X]).eval (nodes j.1) := by
  have hbatch : (batch hk B source : F[X]).eval (nodes j.1) =
      (batch hk B target : F[X]).eval (nodes j.1) := by
    rw [batch_eval, batch_eval]
    apply Finset.sum_congr rfl
    intro i _
    rw [hquery i j]
  change (mask + (batch hk B source - batch hk B target) : DegreeLT F (k+s)).1.eval _ = _
  simp only [Submodule.coe_add, Submodule.coe_sub, eval_add, eval_sub, hbatch, sub_self, add_zero]

/-- The polynomial response evaluates to the primary relation used by
Polygero's opening-only verifier. -/
theorem response_eval (hk : 0 < k) (B : Challenge F m s)
    (rows : Fin m → DegreeLT F k) (mask : DegreeLT F (k+s)) (x : F) :
    (response hk B rows mask : F[X]).eval x =
      (∑ i, (B i : F[X]).eval x * (rows i : F[X]).eval x) + (mask : F[X]).eval x := by
  change ((batch hk B rows : F[X]) + (mask : F[X])).eval x = _
  rw [eval_add, batch_eval]

end LfzkV2.PolygeroPrimaryMasking
