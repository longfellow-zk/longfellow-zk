import LfzkV2.Current.ZeroKnowledge.SHAObserverWindow

/-! Routing consults its fallback only outside the selected SHA domain.
Changing unused coordinates inside that domain therefore leaves the residual
observer syntax, and its finite oracle marginal, unchanged. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.SHAComplement
open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Raw D QT AT Value : Type}
variable (domain : Raw → Prop) (first second : Raw → D)
variable (agree : ∀ raw, ¬domain raw → first raw = second raw)

include agree in
theorem route_eq {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    SHAOracle.route domain first tree = SHAOracle.route domain second tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      by_cases member : domain query
      · simp only [SHAOracle.route,if_pos member]
        congr 1
        funext answer
        exact ih answer
      · simp only [SHAOracle.route,if_neg member]
        rw [agree query member]
        exact congrArg SHAOracle.weakenLeft (ih _)
  | queryRight query next ih =>
      simp only [SHAOracle.route]
      congr 1
      funext answer
      exact ih answer

include agree in
theorem observer_eq {left right : ℕ} (tree : TwoOracleTree Raw D QT AT Value left right) :
    SHAOracle.observer domain first tree = SHAOracle.observer domain second tree :=
  route_eq domain first second agree (Observer.record [] tree)

variable {Request Proof Observed : Type} {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree Raw D QT AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree Raw D QT AT Observed postM postT)

include agree in
theorem trees_eq :
    SHAObserverWindow.trees domain first prior after = SHAObserverWindow.trees domain second prior after := by
  funext index
  cases index with
  | inl value => exact observer_eq domain first second agree prior
  | inr pair => exact observer_eq domain first second agree (after pair.1 pair.2)

variable [Fintype D] [Fintype AT] [DecidableEq Raw]
variable {Salt Leaf : Type}
variable [Fintype Request] [Fintype Proof] [Fintype Salt] [Fintype Leaf]
variable (codec : Codec Salt Leaf D Raw)

include agree in
theorem window_eq :
    SHAObserverWindow.window domain first codec prior after =
      SHAObserverWindow.window domain second codec prior after := by
  unfold SHAObserverWindow.window
  rw [trees_eq domain first second agree prior after]

end LfzkV2.Current.ZeroKnowledge.SHAComplement
