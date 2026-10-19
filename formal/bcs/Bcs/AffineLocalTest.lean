import Bcs.AffinePotential
import Bcs.AffineSingleton
import Lean.Util.CollectAxioms

/-! The localized compilers are kernel proofs, including arbitrary
adaptive schedules and prefix-dependent off-answer contexts. -/
open Lean Elab Command
run_cmd do
  for name in #[
      ``Bcs.TotalOracle.queried_domain_card_le,
      ``Bcs.TotalOracle.charged_two_fresh_weight_expected_le,
      ``Bcs.TotalOracle.tree_first_pair_grouped_domain_le,
      ``Bcs.TotalOracle.tree_child_indexed_weight_domain_le,
      ``Bcs.TotalOracle.tree_both_orders_local_context_domain_le,
      ``Bcs.TotalOracle.tree_two_scale_local_context_final_domain_le,
      ``Bcs.TotalOracle.Footprint.singleton_oracle_sound,
      ``Bcs.AffineBlock.oracle_sound_of_charges,
      ``Bcs.AffineBlock.oracle_sound_of_embedded_charges] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
