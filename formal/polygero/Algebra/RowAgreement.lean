import polygero.Algebra.PolynomialChallenges.Basic
import LigeroFamily.Code.ReedSolomon
import Mathlib.LinearAlgebra.Lagrange

namespace RecursivePolygero
open Polynomial Finset Codes LigeroFamily RecursivePolygero.Local
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] {n m k R t : ℕ}

/-- Simultaneous agreement of all ordinary rows, including arithmetic masks. -/
noncomputable def rowAgreement (C : RSCode F n R) (W : Fin m → Word F n)
    (f : Fin m → DegreeLT F k) : Finset (Fin n) :=
  univ.filter fun j => ∀ i, W i j = (f i : F[X]).eval (C.node j)

/-- Distinct polynomial row tuples share at most `k-1` agreement columns. -/
theorem rowAgreement_inter_card_le (C : RSCode F n R) (W : Fin m → Word F n)
    (f g : Fin m → DegreeLT F k) (hne : f ≠ g) :
    (rowAgreement C W f ∩ rowAgreement C W g).card ≤ k-1 := by
  by_contra hn
  have hsize : k ≤ (rowAgreement C W f ∩ rowAgreement C W g).card := by omega
  apply hne
  funext i
  apply Subtype.ext
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
    (rowAgreement C W f ∩ rowAgreement C W g) C.node_injective.injOn
  · exact (mem_degreeLT.mp (f i).2).trans_le (by exact_mod_cast hsize)
  · exact (mem_degreeLT.mp (g i).2).trans_le (by exact_mod_cast hsize)
  · intro j hj
    have hf := (mem_filter.mp (mem_inter.mp hj).1).2 i
    have hg := (mem_filter.mp (mem_inter.mp hj).2).2 i
    exact hf.symm.trans hg

end RecursivePolygero
