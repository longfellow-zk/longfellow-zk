import LfzkV2.Current.SHAProbability
import Bcs.StatisticalDistance
import Bcs.SameDistribution

/-! Averaging the exact SHA-domain split. Here Query is any finite random-
oracle marginal, not the type of all byte strings. Uniform whole-table
sampling equals independent uniform sampling of its two coordinate slices.
Thus a bound proved for every complementary slice is an unconditional bound
for the whole ideal oracle; no independence of an observed adaptive trace is
assumed by conditioning on that trace. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
open LigeroFamily
open scoped Classical

variable {Query Answer R S View : Type}
variable [Fintype Query] [Fintype Answer] [Fintype R] [Fintype S] [DecidableEq View]
variable (domain : Query → Prop)

theorem split_sameDistribution (observe : (Query → Answer) → View) :
    SameDistribution (fun H : Query → Answer => observe H)
      (fun slices => observe ((SHAOracle.split domain).symm slices)) := by
  apply sameDistribution_of_equiv (SHAOracle.split domain)
  intro H
  rw [Equiv.symm_apply_apply]

omit [DecidableEq View] in
theorem conditional_statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (real : R → (Query → Answer) → View) (simulate : S → (Query → Answer) → View)
    (each : ∀ outside : {query // ¬domain query} → Answer,
      StatClose epsilon
        (fun coin : R × ({query // domain query} → Answer) =>
          real coin.1 ((SHAOracle.split domain).symm (coin.2,outside)))
        (fun coin : S × ({query // domain query} → Answer) =>
          simulate coin.1 ((SHAOracle.split domain).symm (coin.2,outside)))) :
    StatClose epsilon (fun coin : R × (Query → Answer) => real coin.1 coin.2)
      (fun coin : S × (Query → Answer) => simulate coin.1 coin.2) := by
  have mixed := statClose_mix nonnegative
    (fun outside (coin : R × ({query // domain query} → Answer)) =>
      real coin.1 ((SHAOracle.split domain).symm (coin.2,outside)))
    (fun outside (coin : S × ({query // domain query} → Answer)) =>
      simulate coin.1 ((SHAOracle.split domain).symm (coin.2,outside))) each
  apply statClose_reindex (SHAProbability.coinsEquiv (R := R) domain) (SHAProbability.coinsEquiv (R := S) domain) ?_ ?_ mixed
  · intro coin
    change real coin.1 coin.2 = real coin.1 ((SHAOracle.split domain).symm ((SHAOracle.split domain) coin.2))
    rw [Equiv.symm_apply_apply]
  · intro coin
    change simulate coin.1 coin.2 = simulate coin.1 ((SHAOracle.split domain).symm ((SHAOracle.split domain) coin.2))
    rw [Equiv.symm_apply_apply]

omit [DecidableEq View] in
/-- Unused coordinates of a larger finite oracle table cost nothing. The
selected marginal may depend on the already-fixed complementary SHA slice;
this theorem is applied separately at each such slice before averaging. -/
theorem restriction_statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (real : R → ({query // domain query} → Answer) → View)
    (simulate : S → ({query // domain query} → Answer) → View)
    (restricted : StatClose epsilon (fun coin : R × ({query // domain query} → Answer) => real coin.1 coin.2)
      (fun coin : S × ({query // domain query} → Answer) => simulate coin.1 coin.2)) :
    StatClose epsilon
      (fun coin : R × (Query → Answer) => real coin.1 (fun query => coin.2 query.val))
      (fun coin : S × (Query → Answer) => simulate coin.1 (fun query => coin.2 query.val)) := by
  apply conditional_statClose domain nonnegative
    (fun r H => real r (fun query => H query.val))
    (fun s H => simulate s (fun query => H query.val))
  intro outside
  have read (inside : {query // domain query} → Answer) :
      (fun query : {query // domain query} => ((SHAOracle.split domain).symm (inside,outside)) query.val) = inside := by
    funext query
    simp only [SHAOracle.split,Equiv.coe_fn_symm_mk,dif_pos query.property]
  simpa only [read] using restricted

end LfzkV2.Current.ZeroKnowledge.SHAOracleProbability
