import LfzkV2.Current.MdocBudgets
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext

/-! Two limits of the current numerical analysis. A quadratic false-round
residual can have two roots, so its local `2/q` estimate cannot generally be
replaced by `1/q`. The rounded global expression does lose a small amount
when replacing the exact nonzero-challenge denominator. Neither observation
claims an attack attaining the complete protocol bound. -/
namespace LfzkV2.Current.Tests.Tightness
open Finset
open scoped Classical

example {F : Type} [Field F] [Fintype F] (a : F) (nonzero : a ≠ 0) :
    (univ.filter fun r : F => r*(r-a) = 0).card = 2 := by
  classical
  have roots : (univ.filter fun r : F => r*(r-a) = 0) = {0,a} := by
    ext r
    simp only [mem_filter,mem_univ,true_and,mul_eq_zero,sub_eq_zero,mem_insert,mem_singleton]
  rw [roots,card_pair (Ne.symm nonzero)]

example {F : Type} [Field F] (a : F) (notOne : a ≠ 1) :
    (0:F)*(0-a)+1*(1-a) ≠ 0 := by
  simpa only [zero_mul,one_mul,zero_add,sub_ne_zero] using Ne.symm notOne

example (q : ℚ) (large : 1 < q) (Q : ℕ) :
    (Q:ℚ)*(2/(q-1))+((Q:ℚ)+1)/q^2 =
      2*Q/q+(3*Q+1)/q^2+2*Q/(q^2*(q-1)) := by
  have nonzero : q ≠ 0 := ne_of_gt (lt_trans (by norm_num) large)
  have different : q-1 ≠ 0 := ne_of_gt (sub_pos.mpr large)
  field_simp [nonzero,different]
  ring

end LfzkV2.Current.Tests.Tightness
