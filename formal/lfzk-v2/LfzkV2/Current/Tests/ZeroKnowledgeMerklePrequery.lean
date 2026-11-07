import LfzkV2.Current.ZeroKnowledge.MerklePrequery

/-! The prior observer repeats a query and then chooses the next location
from the answer.  Refreshing that new location preserves both old answers.
An attempt to refresh the repeated location must instead keep its old answer. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerklePrequery

open Merkle.RandomOracle ZeroKnowledge.MerklePrequery
open scoped Classical

def prior : Tree (Fin 3) Bool (Fin 3) 2 :=
  .query 0 fun bit => .query 0 fun _ => .done (if bit then 1 else 2)

theorem priorFresh (H : Fin 3 → Bool) : fresh prior id H := by
  by_cases bit : H 0 = true
  · simp [fresh,location,prior,Tree.run_query,bit]
  · have no : H 0 = false := Bool.eq_false_iff.mpr bit
    simp [fresh,location,prior,Tree.run_query,no]

example (coins : (Fin 3 → Bool) × Bool) :
    prior.run (swap prior id coins).1 = prior.run coins.1 := prior_swap prior id coins

example (coins : (Fin 3 → Bool) × Bool) :
    (swap prior id coins).1 (if coins.1 0 then 1 else 2) = coins.2 := by
  simpa [location,prior,Tree.run_query] using
    programmed_answer prior id coins (priorFresh coins.1)

def repeats : Tree (Fin 3) Bool (Fin 3) 1 := .query 0 fun _ => .done 0

example (coins : (Fin 3 → Bool) × Bool) : swap repeats id coins = coins := by
  simp [swap,fresh,location,repeats,Tree.run_query]

example : LigeroFamily.SameDistribution
    (fun coins : (Fin 3 → Bool) × Bool =>
      (prior.run coins.1,refreshedAnswer prior id coins,(swap prior id coins).1))
    (fun coins : (Fin 3 → Bool) × Bool =>
      (prior.run coins.1,coins.1 (location prior id coins.1),coins.1)) :=
  refresh_sameDistribution prior id (fun history answer H => (history,answer,H))

#print axioms refresh_sameDistribution
#print axioms swap_involutive

end LfzkV2.Current.Tests.ZeroKnowledgeMerklePrequery
