import polygero.Recursion.FSTerminalBlock
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit actual whole-child-block charging, including all private helpers. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``Bcs.AffineBlock.oracle_sound_of_footprints, #[
        ``Bcs.TotalOracle.Footprint.event_le_expected_budget,
        ``Bcs.TotalOracle.Footprint.activated_budget_domain_le]),
      (``Bcs.TerminalCharges.normalized_block_average, #[
        ``Bcs.TotalOracle.Footprint.average_two_eval,
        ``Bcs.TerminalCharges.excessPrice_mul]),
      (``RecursivePolygero.FiatShamir.TwoLevel.terminal_block_oracle_sound, #[
        ``Bcs.AffineBlock.oracle_sound_of_footprints]),
      (``RecursivePolygero.FiatShamir.TwoLevel.rigidChildBlockWeight_local_eq, #[
        ``Bcs.TerminalCharges.normalized_block_average]),
      (``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlockWeight_local_le, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.rigidChildBlockWeight_local_eq]),
      (``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlock_pay, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.high_child_rigid_or_nonrigid,
        ``Bcs.TerminalCharges.basePrice_ge_threshold]),
      (``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_of_mean, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.terminal_block_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlockWeight_local_le,
        ``RecursivePolygero.FiatShamir.TwoLevel.normalizedChildBaseWeight_local,
        ``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlock_pay]),
      (``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_of_mean,
        ``RecursivePolygero.ProfileAnalysis.fixed_rigidBlockCharge_mean_le,
        ``RecursivePolygero.ProfileAnalysis.responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`Bcs.TerminalCharges, `polygero.Recursion.FSTerminalBlock].contains owner do
      continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
