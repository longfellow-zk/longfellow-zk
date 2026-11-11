import LfzkV2.Current.ZeroKnowledge.SHAGlobalWindow
import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Average a bound for every complementary oracle over a larger finite
SHA table. The small marginal is fixed before sampling. The complement may
determine public setup, observer programs, and metadata; none is obtained by
conditioning on the answers in an observed execution. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability
open LigeroFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] StatClose probOf

variable {Raw Answer R S View : Type}
variable [DecidableEq Raw] [Fintype Answer] [Fintype R] [Fintype S]
variable (small large : Finset Raw) (contains : small ⊆ large)

include contains in
/-- A uniform bound for every fixed complement holds for one uniform
larger SHA table, including its public-setup and observer coordinates.
Both experiments receive that same table throughout their execution. -/
theorem window_statClose_of_extension {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (fallback : Raw → Answer)
    (real : R → (Raw → Answer) → View) (simulate : S → (Raw → Answer) → View)
    (each : ∀ table : {raw // raw ∈ large} → Answer, StatClose epsilon
      (fun coin : R × ({raw // raw ∈ small} → Answer) =>
        real coin.1 (OracleWindow.extend small coin.2 (OracleWindow.extend large table fallback)))
      (fun coin : S × ({raw // raw ∈ small} → Answer) =>
        simulate coin.1 (OracleWindow.extend small coin.2 (OracleWindow.extend large table fallback)))) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ large} → Answer) =>
        real coin.1 (OracleWindow.extend large coin.2 fallback))
      (fun coin : S × ({raw // raw ∈ large} → Answer) =>
        simulate coin.1 (OracleWindow.extend large coin.2 fallback)) := by
  classical
  have conditional (outside : {raw : {raw // raw ∈ large} // raw.val ∉ small} → Answer) :
      StatClose epsilon
        (fun coin : R × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer) =>
          real coin.1 (OracleWindow.extend large
            ((SHAOracle.split (fun raw : {raw // raw ∈ large} => raw.val ∈ small)).symm (coin.2,outside)) fallback))
        (fun coin : S × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer) =>
          simulate coin.1 (OracleWindow.extend large
            ((SHAOracle.split (fun raw : {raw // raw ∈ large} => raw.val ∈ small)).symm (coin.2,outside)) fallback)) := by
    let e := SHAProbability.inclusionEquiv small large contains
    let changeR := Equiv.prodCongr (Equiv.refl R) (Equiv.arrowCongr e (Equiv.refl Answer))
    let changeS := Equiv.prodCongr (Equiv.refl S) (Equiv.arrowCongr e (Equiv.refl Answer))
    have law := each (SHAProbability.outsideTable small large fallback outside)
    apply Probability.changeFintype (statClose_reindex changeR.symm changeS.symm ?_ ?_ law)
    · intro coin
      rw [SHAProbability.extend_split small large contains]
      rfl
    · intro coin
      rw [SHAProbability.extend_split small large contains]
      rfl
  let predicate := fun raw : {raw // raw ∈ large} => raw.val ∈ small
  have mixed := statClose_mix nonnegative
    (fun outside (coin : R × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer)) =>
      real coin.1 (OracleWindow.extend large ((SHAOracle.split predicate).symm (coin.2,outside)) fallback))
    (fun outside (coin : S × ({raw : {raw // raw ∈ large} // raw.val ∈ small} → Answer)) =>
      simulate coin.1 (OracleWindow.extend large ((SHAOracle.split predicate).symm (coin.2,outside)) fallback)) conditional
  apply statClose_reindex
    (SHAProbability.coinsEquiv (R := R) (Answer := Answer) predicate)
    (SHAProbability.coinsEquiv (R := S) (Answer := Answer) predicate) ?_ ?_ mixed
  · intro coin
    change real coin.1 (OracleWindow.extend large coin.2 fallback) =
      real coin.1 (OracleWindow.extend large
        ((SHAOracle.split predicate).symm ((SHAOracle.split predicate) coin.2)) fallback)
    rw [Equiv.symm_apply_apply]
  · intro coin
    change simulate coin.1 (OracleWindow.extend large coin.2 fallback) =
      simulate coin.1 (OracleWindow.extend large
        ((SHAOracle.split predicate).symm ((SHAOracle.split predicate) coin.2)) fallback)
    rw [Equiv.symm_apply_apply]

include contains in
/-- A uniform bound for every fixed complement holds for one uniform
larger SHA table, including its public-setup and observer coordinates.
Both experiments receive that same table throughout their execution. -/
theorem window_statClose {epsilon : ℚ} (nonnegative : 0 ≤ epsilon)
    (fallback : Raw → Answer)
    (real : R → (Raw → Answer) → View) (simulate : S → (Raw → Answer) → View)
    (each : ∀ outside : Raw → Answer, StatClose epsilon
      (fun coin : R × ({raw // raw ∈ small} → Answer) =>
        real coin.1 (OracleWindow.extend small coin.2 outside))
      (fun coin : S × ({raw // raw ∈ small} → Answer) =>
        simulate coin.1 (OracleWindow.extend small coin.2 outside))) :
    StatClose epsilon
      (fun coin : R × ({raw // raw ∈ large} → Answer) =>
        real coin.1 (OracleWindow.extend large coin.2 fallback))
      (fun coin : S × ({raw // raw ∈ large} → Answer) =>
        simulate coin.1 (OracleWindow.extend large coin.2 fallback)) := by
  exact window_statClose_of_extension small large contains nonnegative fallback real simulate
    (fun table => each (OracleWindow.extend large table fallback))

end LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability
