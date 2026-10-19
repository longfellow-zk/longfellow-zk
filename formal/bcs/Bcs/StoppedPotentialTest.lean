import Bcs.StoppedPotential
import Bcs.StoppedCharges
import Bcs.TwoStageSearch
import Bcs.FreshSearch
import Bcs.GrindingBounds
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Kernel and dependency audits for stopped amortization and the fresh
adaptive-search bridge. In particular, the ROM bridge must use the actual
off-coordinate counting identity, rather than an assumed sampling rule. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``Bcs.StoppedPotential.stoppedValue_le, #[
        ``Bcs.StoppedPotential.stoppedValue,
        ``Bcs.TotalOracle.Footprint.average_mono]),
      (``Bcs.StoppedPotential.repeatPrice_child_step, #[
        ``Bcs.StoppedPotential.repeatPrice,
        ``Bcs.StoppedPotential.repeat_child_step_iff]),
      (``Bcs.StoppedPotential.average_repeatPrice_le, #[
        ``Bcs.StoppedPotential.repeatPrice_le_of_child]),
      (``Bcs.StoppedPotential.fresh_parent_best_step, #[
        ``Bcs.StoppedPotential.repeatPrice_nonneg]),
      (``Bcs.StoppedPotential.renewal_rate_lower_bound, #[
        ``Bcs.StoppedPotential.repeat_child_step_iff]),
      (``Bcs.StoppedPotential.small_scalar_mean_counterexample, #[
        ``Bcs.StoppedPotential.renewal_rate_lower_bound]),
      (``Bcs.StoppedCharges.oracle_sound, #[
        ``Bcs.AffineBlock.oracle_sound_of_embedded_charges,
        ``Bcs.StoppedPotential.repeatPrice_child_step]),
      (``Bcs.TwoStageSearch.all_samples_mass, #[
        ``Fintype.sum_pow, ``Fintype.prod_boole]),
      (``Bcs.TwoStageSearch.selected_row_search_mass_uniform, #[
        ``Bcs.TotalOracle.Footprint.average_eval,
        ``Bcs.TwoStageSearch.any_sample_mass]),
      (``Bcs.TotalOracle.FreshSearch.totalOracle_eq_iid, #[
        ``Bcs.TotalOracle.FreshSearch.avoids_seen,
        ``Bcs.TotalOracle.run_eq_of_not_mem])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  let bridge := ``Bcs.TotalOracle.FreshSearch.totalOracle_eq_iid
  let some info := env.find? bridge | throwError "Missing theorem {bridge}"
  let some counter := info.getUsedConstantsAsSet.toList.find? (fun name =>
      name.toString.endsWith ".average_off_coordinate") |
    throwError "Fresh ROM bridge omits its actual coordinate-counting step"
  let some countInfo := env.find? counter | throwError "Missing helper {counter}"
  unless countInfo.getUsedConstantsAsSet.contains ``Bcs.TotalOracle.sum_coord_mul_rat do
    throwError "Fresh ROM bridge does not use the rational coordinate-counting identity"
  let modules := #[`Bcs.StoppedPotential, `Bcs.StoppedCharges, `Bcs.TwoStageSearch,
    `Bcs.FreshSearch, `Bcs.GrindingBounds]
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless modules.contains owner do continue
    if info.isAxiom then throwError "Unexpected stopped/search axiom: {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
