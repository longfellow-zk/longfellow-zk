import LfzkV2.Current.ZeroKnowledge.MerklePrequery

/-! Whole-answer refresh with an aborting causal prefix. On an abort the
oracle is left unchanged. On an active fresh branch one answer is exchanged
with the independent whole-answer coin. Whether the branch is active is
computed from the earlier program's result and is preserved by the exchange.
This avoids programming a hidden dummy location after a failed parser. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefreshActive
open Merkle.RandomOracle
open scoped Classical
variable {Query Answer Result View : Type} {fuel : ℕ}
variable (before : Tree Query Answer Result fuel) (input : Result → Query) (active : Result → Prop)

def swap (coins : (Query → Answer) × Answer) : (Query → Answer) × Answer :=
  if active (before.run coins.1).1 then MerklePrequery.swap before input coins else coins

theorem prior_swap (coins : (Query → Answer) × Answer) :
    before.run (swap before input active coins).1 = before.run coins.1 := by
  unfold swap
  split_ifs
  · exact MerklePrequery.prior_swap before input coins
  · rfl

theorem swap_involutive : Function.Involutive (swap before input active) := by
  intro coins
  by_cases enabled : active (before.run coins.1).1
  · have still : active (before.run (MerklePrequery.swap before input coins).1).1 := by
      rw [MerklePrequery.prior_swap]
      exact enabled
    simp only [swap,enabled,still,↓reduceIte,MerklePrequery.swap_involutive before input coins]
  · simp only [swap,enabled,↓reduceIte]

def swapEquiv : ((Query → Answer) × Answer) ≃ ((Query → Answer) × Answer) where
  toFun := swap before input active
  invFun := swap before input active
  left_inv := swap_involutive before input active
  right_inv := swap_involutive before input active

variable (observe : (Result × List (Query × Answer)) → Option Answer → (Query → Answer) → View)

def honest (coins : (Query → Answer) × Answer) : View :=
  let earlier := before.run coins.1
  observe earlier (if active earlier.1 then some (coins.1 (input earlier.1)) else none) coins.1

def guarded (coins : (Query → Answer) × Answer) : View :=
  let earlier := before.run coins.1
  observe earlier (if active earlier.1 then some (MerklePrequery.refreshedAnswer before input coins) else none)
    (swap before input active coins).1

def programmed (coins : (Query → Answer) × Answer) : View :=
  let earlier := before.run coins.1
  observe earlier (if active earlier.1 then some coins.2 else none)
    (if active earlier.1 then Function.update coins.1 (input earlier.1) coins.2 else coins.1)

theorem guarded_after_swap (coins : (Query → Answer) × Answer) :
    guarded before input active observe coins = honest before input active observe (swap before input active coins) := by
  unfold guarded honest
  rw [prior_swap]
  by_cases enabled : active (before.run coins.1).1
  · simp only [enabled,↓reduceIte,swap,MerklePrequery.refreshedAnswer_eq]
    rw [MerklePrequery.location_swap]
    rfl
  · simp only [enabled,↓reduceIte]

theorem guarded_sameDistribution [Fintype Query] [Fintype Answer] [DecidableEq View] :
    LigeroFamily.SameDistribution (guarded before input active observe) (honest before input active observe) := by
  apply LigeroFamily.sameDistribution_of_equiv (swapEquiv before input active)
  exact guarded_after_swap before input active observe

theorem programmed_eq_guarded (coins : (Query → Answer) × Answer)
    (unused : active (before.run coins.1).1 → MerklePrequery.fresh before input coins.1) :
    programmed before input active observe coins = guarded before input active observe coins := by
  by_cases enabled : active (before.run coins.1).1
  · have fresh := unused enabled
    simp only [programmed,guarded,swap,enabled,↓reduceIte,MerklePrequery.swap,
      MerklePrequery.refreshedAnswer,fresh,MerklePrequery.location]
  · simp only [programmed,guarded,swap,enabled,↓reduceIte]

theorem disagreement_active_hit (coins : (Query → Answer) × Answer)
    (different : programmed before input active observe coins ≠ guarded before input active observe coins) :
    active (before.run coins.1).1 ∧ ¬ MerklePrequery.fresh before input coins.1 := by
  by_cases enabled : active (before.run coins.1).1
  · refine ⟨enabled,?_⟩
    intro fresh
    exact different (programmed_eq_guarded before input active observe coins (fun _ => fresh))
  · exact (different (programmed_eq_guarded before input active observe coins (fun h => (enabled h).elim))).elim

end LfzkV2.Current.ZeroKnowledge.OracleRefreshActive
