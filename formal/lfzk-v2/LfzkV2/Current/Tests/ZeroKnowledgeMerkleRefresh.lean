import LfzkV2.Current.ZeroKnowledge.MerkleRefresh
import LfzkV2.Current.ZeroKnowledge.MerklePriorHits
import Mathlib.Tactic.FinCases

/-! Refresh the two honest queries after an earlier observer query. The
independent experiment proves freshness; it is not supplied by a certificate
about the refreshed oracle. The observer's complete old trace is retained. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleRefresh

open Merkle.RandomOracle ZeroKnowledge.MerkleRefresh
open scoped Classical

def before : Tree (Fin 3) Bool Unit 1 := .query 0 fun _ => .done ()

def input (count : ℕ) (_ : Unit) : Fin 3 := if count = 0 then 1 else 2

def update (_ : ℕ) (_ : Unit) (_ : Bool) : Unit := ()

theorem sampled_fresh (coins : (Fin 3 → Bool) × (Fin 2 → Bool)) :
    ∀ i : Fin 2, ∀ qa ∈
      (sampledRun input update (before.run coins.1) coins.2 i.val (Nat.le_of_lt i.isLt)).2,
      qa.1 ≠ input i.val
        (sampledRun input update (before.run coins.1) coins.2 i.val (Nat.le_of_lt i.isLt)).1 := by
  intro i
  fin_cases i <;> simp [sampledRun,input,update,before,Tree.run_query,Tree.run_done]

example (coins : (Fin 3 → Bool) × (Fin 2 → Bool)) :
    (history before input update 2).run (refresh before input update 2 (le_refl _) coins).1 =
      sampledRun input update (before.run coins.1) coins.2 2 (le_refl _) := by
  apply sampled_run
  exact fresh_of_sampled before input update coins (sampled_fresh coins)

example (coins : (Fin 3 → Bool) × (Fin 2 → Bool)) :
    before.run (refresh before input update 2 (le_refl _) coins).1 = before.run coins.1 :=
  prior_refresh before input update 2 (le_refl _) coins

#print axioms fresh_of_sampled
#print axioms refresh_sameDistribution
#print axioms refresh_outside
#print axioms ZeroKnowledge.MerklePriorHits.nodes_card_le

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleRefresh
