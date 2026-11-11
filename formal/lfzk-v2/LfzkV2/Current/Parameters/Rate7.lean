import LfzkV2.Current.Parameters.Rate7.Active
import LfzkV2.Current.Parameters.Rate7.Binary
import LfzkV2.Current.Parameters.Rate7.Prime
import LfzkV2.Current.CertifiedProfile


/-! Assemble the exact rate-1/7 certificate. The independent Hahn checks live
in separate modules so runtime changes do not recheck all polynomial identities. -/

noncomputable section

namespace LfzkV2.Current.FixedRate.Rate7

open RecursivePolygero CodingTheory.HahnDelsarte ParameterBounds

set_option maxRecDepth 100000

set_option maxHeartbeats 0






/-- The complete numerical coding certificate. The two witness-selection
lists are kept separate from the larger active joint-label family. -/
def certificate : CertifiedProfile where
  rate := 7
  k := 349
  s := 12
  n := 2443
  t := 84
  rate_eq := by decide
  activeCutoff := 867
  activeList := 1272737905242889781956743699885451
  binaryCutoff := 865
  primeCutoff := 863
  binaryList := 21898356682154715916
  primeList := 451457457136012100305
  positive_degree := by decide
  query_pos := by decide
  large_le_active := by decide
  active_le_columns := by decide
  active_list_le_field := by norm_num [Adapter.Mdoc.binaryOrder]
  active_bound := Active.family_bound.of_le_size (by decide) (by decide)
  binary_candidates := Binary.family_bound.of_le_size (by decide) (by decide)
  prime_candidates := Prime.family_bound.of_le_size (by decide) (by decide)
  binary_overlap_lt := by decide
  prime_overlap_lt := by decide
  threshold_condition := by
    refine ⟨1, by norm_num, by norm_num, ?_⟩
    simp only [DiscreteThreshold.candidate, tail, Nat.choose_eq_fast_choose]
    decide +kernel
  threshold_lt_one := by
    simp only [tail, Nat.choose_eq_fast_choose]
    decide +kernel
  binary_rank_small := by
    simp only [rankError, Adapter.Mdoc.binaryOrder, Nat.choose_eq_fast_choose]
    decide +kernel
  prime_rank_small := by
    simp only [rankError, Adapter.Mdoc.primeOrder, Nat.choose_eq_fast_choose]
    decide +kernel
  parent_budget_le := by
    simp only [parentBudget, rankError, tail, Adapter.Mdoc.binaryOrder,
      Adapter.Mdoc.primeOrder, Nat.choose_eq_fast_choose]
    decide +kernel
  opening_budget_le := by
    simp only [openingBudget, tail, Adapter.Mdoc.binaryOrder, Nat.choose_eq_fast_choose]
    decide +kernel
  fingerprint_budget_le := by
    simp only [Adapter.Mdoc.binaryOrder, Adapter.Mdoc.primeOrder, Nat.choose_eq_fast_choose]
    decide +kernel

end LfzkV2.Current.FixedRate.Rate7
