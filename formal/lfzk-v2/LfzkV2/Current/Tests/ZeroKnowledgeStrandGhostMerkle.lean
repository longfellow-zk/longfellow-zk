import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleProbability
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleDomains
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSlice
import Lean.Util.CollectAxioms

/-! Public APIs and trusted-kernel dependency checks for indexed leaf-only
programming. These tests intentionally include full prior/later traces,
response-selected openings, and the numbered canonical final seal. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandGhostMerkle
open LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle

#check Swap.swap_involutive
#check Swap.before_swap
#check Tree.installAll_commit
#check Tree.installAll_opening
#check Nonce.hit_card_mul_le
#check Nonce.hit_ratio_le
#check Observer.observer_eq_of_no_hit
#check History.prior_preserved
#check Schedule.honest_coupled_eq_ghost
#check Schedule.honest_coupled_eq_simulate
#check Swap.Slice.lift_swap
#check Swap.Slice.swap_involutive
#check Probability.statistical_hiding_slice
#check Domains.inputOther
#check Domains.oracle_congr
#check Domains.finish_congr
#check LfzkV2.Current.ZeroKnowledge.StrandCompletion.finish_valid

#print axioms Swap.swap_involutive
#print axioms Swap.before_swap
#print axioms Tree.installAll_commit
#print axioms Tree.installAll_opening
#print axioms Nonce.hit_ratio_le
#print axioms Schedule.honest_coupled_eq_ghost
#print axioms Domains.finish_congr
#print axioms LfzkV2.Current.ZeroKnowledge.StrandCompletion.finish_valid

open Lean Elab Command in
run_cmd do
  for endpoint in #[``Swap.Slice.lift_swap, ``Swap.Slice.swap_involutive,
      ``Probability.statistical_hiding_slice] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandGhostMerkle
