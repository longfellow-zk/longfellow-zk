import Merkle.RandomOracle
import Bcs.SameDistribution

/-! Fresh hash evaluation after an arbitrary earlier oracle computation.
Public requests may be chosen by that earlier computation.  Swapping a fresh
oracle coordinate with an independent answer coin is a genuine involution;
it preserves the earlier output and every previously returned answer.

This is the one-query sampling step needed to move honest, causal Merkle
construction to independently sampled labels after a prior-query stage.
It is not by itself a bound on hitting a previously occupied coordinate.
Inputs depending on the answer being programmed are deliberately excluded. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerklePrequery

open Merkle.RandomOracle
open scoped Classical

variable {Query Answer Request : Type} {fuel : ℕ}
variable (before : Tree Query Answer Request fuel) (input : Request → Query)

def location (H : Query → Answer) : Query := input (before.run H).1

def fresh (H : Query → Answer) : Prop :=
  ∀ qa ∈ (before.run H).2, qa.1 ≠ location before input H

theorem prior_update (H : Query → Answer) (answer : Answer) (unused : fresh before input H) :
    before.run (Function.update H (location before input H) answer) = before.run H := by
  apply Tree.run_congr_on_trace
  intro qa member
  rw [Function.update_of_ne (unused qa member)]
  exact (Tree.trace_sound before H qa member).symm

theorem location_update (H : Query → Answer) (answer : Answer) (unused : fresh before input H) :
    location before input (Function.update H (location before input H) answer) =
      location before input H := by
  exact congrArg (fun result => input result.1) (prior_update before input H answer unused)

theorem fresh_update (H : Query → Answer) (answer : Answer) (unused : fresh before input H) :
    fresh before input (Function.update H (location before input H) answer) := by
  unfold fresh
  rw [prior_update before input H answer unused,location_update before input H answer unused]
  exact unused

/-- On a collision with the old table do nothing. This makes the coupling a
total equivalence rather than assuming that the simulator always succeeds. -/
def swap (coins : (Query → Answer) × Answer) : (Query → Answer) × Answer :=
  if fresh before input coins.1 then
    (Function.update coins.1 (location before input coins.1) coins.2,
      coins.1 (location before input coins.1))
  else coins

theorem swap_involutive : Function.Involutive (swap before input) := by
  intro coins
  rcases coins with ⟨H,answer⟩
  by_cases unused : fresh before input H
  · have hn := fresh_update before input H answer unused
    have hl := location_update before input H answer unused
    simp only [swap,unused,hn,↓reduceIte,hl,Function.update_self]
    apply Prod.ext
    · funext query
      by_cases same : query = location before input H
      · subst query
        simp
      · simp [same]
    · rfl
  · simp only [swap,unused,↓reduceIte]

def swapEquiv : ((Query → Answer) × Answer) ≃ ((Query → Answer) × Answer) where
  toFun := swap before input
  invFun := swap before input
  left_inv := swap_involutive before input
  right_inv := swap_involutive before input

theorem prior_swap (coins : (Query → Answer) × Answer) :
    before.run (swap before input coins).1 = before.run coins.1 := by
  unfold swap
  split_ifs with unused
  · exact prior_update before input coins.1 coins.2 unused
  · rfl

theorem location_swap (coins : (Query → Answer) × Answer) :
    location before input (swap before input coins).1 = location before input coins.1 := by
  exact congrArg (fun result => input result.1) (prior_swap before input coins)

theorem programmed_answer (coins : (Query → Answer) × Answer)
    (unused : fresh before input coins.1) :
    (swap before input coins).1 (location before input coins.1) = coins.2 := by
  simp only [swap,unused,↓reduceIte,Function.update_self]

/-- Refresh a new coordinate; retain the old answer on a repeated query.
The latter branch is essential: an already answered query is never resampled. -/
def refreshedAnswer (coins : (Query → Answer) × Answer) : Answer :=
  if fresh before input coins.1 then coins.2 else coins.1 (location before input coins.1)

theorem refreshedAnswer_eq (coins : (Query → Answer) × Answer) :
    refreshedAnswer before input coins =
      (swap before input coins).1 (location before input (swap before input coins).1) := by
  rw [location_swap]
  by_cases unused : fresh before input coins.1
  · simpa only [refreshedAnswer,unused,↓reduceIte] using
      (programmed_answer before input coins unused).symm
  · simp only [refreshedAnswer,swap,unused,↓reduceIte]

/-- The entire oracle remains observable after refreshing.  In particular,
this statement preserves arbitrary subsequent adaptive queries, not merely
the distribution of the selected answer.  The prior request may itself have
been chosen adaptively using every earlier answer.

Finite query types represent the finite oracle window of an experiment; the
coordinate-swap lemmas above do not need that restriction.  This is an exact
sampling statement, leaving the probability of the repeated-query branch to
the protocol-specific freshness bound. -/
theorem refresh_sameDistribution [DecidableEq Query] [Fintype Query] [Fintype Answer]
    {View : Type} [DecidableEq View]
    (observe : (Request × List (Query × Answer)) → Answer → (Query → Answer) → View) :
    LigeroFamily.SameDistribution
      (fun coins : (Query → Answer) × Answer =>
        observe (before.run coins.1) (refreshedAnswer before input coins)
          (swap before input coins).1)
      (fun coins : (Query → Answer) × Answer =>
        observe (before.run coins.1) (coins.1 (location before input coins.1)) coins.1) := by
  apply LigeroFamily.sameDistribution_of_equiv (swapEquiv before input)
  intro coins
  change observe (before.run coins.1) (refreshedAnswer before input coins)
      (swap before input coins).1 =
    observe (before.run (swap before input coins).1)
      ((swap before input coins).1 (location before input (swap before input coins).1))
      (swap before input coins).1
  rw [prior_swap,refreshedAnswer_eq]

end LfzkV2.Current.ZeroKnowledge.MerklePrequery
