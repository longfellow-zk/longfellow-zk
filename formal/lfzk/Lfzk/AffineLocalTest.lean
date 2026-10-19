import Lfzk.AffineForkHybrid
import Lfzk.Fork.Test
import Lfzk.V1StrongV7ContextFinal
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Check actual charge/count dependencies and inherited numerical trust.
The conditional affine hybrid wrapper remains separate; Fork.Test audits
the concrete end-to-end forked commitment theorem. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``Lfzk.AffineSide.side_oracle_sound, #[
        ``Lfzk.RbrZkFlat.sidePointCharge_uniform_local,
        ``Lfzk.RbrZkFlat.accepted_noSat_sideTrace_pays,
        ``Bcs.AffineBlock.oracle_sound_of_embedded_charges]),
      (``Lfzk.AffineSide.field_oracle_sound, #[
        ``Lfzk.RbrZkFlat.sideFieldPointCharge_uniform_local,
        ``Lfzk.RbrZkFlat.fieldPrefixEscape_sideFieldTrace_pays]),
      (``Lfzk.AffineLocal.ligero_oracle_sound, #[
        ``Lfzk.V1StrongV7LowQuery.decoded_low_query_le,
        ``Lfzk.V1StrongV7HighCount.v7_v1_high_count_le,
        ``Bcs.TotalOracle.tree_two_scale_local_context_final_domain_le]),
      (``Lfzk.AffineMac.mac_oracle_sound, #[
        ``Lfzk.NizkZkDeployedHash.twoFieldMacKey_local,
        ``Bcs.TotalOracle.Footprint.singleton_oracle_sound]),
      (``Lfzk.AffineFork.forked_circuits_bound, #[
        ``Lfzk.AffineSide.side_oracle_sound,
        ``Bcs.AffineBlock.oracle_parallel_certificate,
        ``Bcs.AffineBlock.queryCost_sum_le]),
      (``Lfzk.AffineFork.forked_agreement_bound, #[
        ``Lfzk.AffineSide.side_oracle_sound,
        ``Lfzk.AffineMac.mac_oracle_sound,
        ``Bcs.AffineBlock.oracle_parallel]),
      (``Lfzk.AffineFork.hybrid_bound_116, #[
        ``Bcs.AffineBlock.oracle_parallel,
        ``Lfzk.AffineFork.hybridRates_le,
        ``Lfzk.V1StrongV7Hash1HybridNumeric.rhs_le_116])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for name in #[
      ``Lfzk.AffineSide.side_oracle_sound,
      ``Lfzk.AffineSide.field_oracle_sound,
      ``Lfzk.AffineSide.sideRate_le_density,
      ``Lfzk.AffineMac.mac_oracle_sound,
      ``Lfzk.AffineFork.forked_circuits_bound,
      ``Lfzk.AffineFork.forked_agreement_bound,
      ``Lfzk.AffineFork.blockDomains_disjoint] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
  let inherited ← collectAxioms ``Lfzk.V1StrongV7ContextFinal.v7_v1_context_final_density_le
  let numeric ← collectAxioms ``Lfzk.V1StrongV7Hash1HybridNumeric.rhs_le_116
  let mass ← collectAxioms ``Lfzk.V1StrongV7Numeric.density_lt_six
  let grid ← collectAxioms ``Lfzk.GradedCoreGrid.v7GradedCosts_le_coefficient
  for name in #[
      ``Lfzk.AffineLocal.ligero_oracle_sound,
      ``Lfzk.AffineLocal.transcript_ligero_oracle_sound,
      ``Lfzk.AffineFork.hybridRates_le,
      ``Lfzk.AffineFork.hybrid_bound_116,
      ``Lfzk.AffineFork.hybrid_bound_with_commit_116] do
    for ax in ← collectAxioms name do
      if ax == ``sorryAx then throwError "Unfinished proof in {name}"
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound ||
          inherited.contains ax || numeric.contains ax || grid.contains ax || mass.contains ax do
        throwError "New numerical axiom {ax} in {name}"
