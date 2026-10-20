import polygero.Instances.FSCompletion81
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the actual completion, algebra, numerical and IOP bridges. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``Bcs.TotalOracle.Footprint.trace_completion_average_le, #[
        ``Bcs.TotalOracle.Footprint.selected_unseen_average_le,
        ``Bcs.TotalOracle.Footprint.run_eq_of_avoids]),
      (``Bcs.AffineBlock.oracle_sound_of_pair_completion, #[
        ``Bcs.AffineBlock.oracle_sound_of_completion,
        ``Bcs.TotalOracle.Footprint.trace_completion_average_le,
        ``Bcs.TotalOracle.Footprint.singleton_completion_mean]),
      (``Bcs.StoppedCharges.oracle_sound_joint, #[
        ``Bcs.AffineBlock.oracle_sound_of_embedded_pair_completion]),
      (``RecursivePolygero.FiatShamir.TwoLevel.query_joint_oracle_sound, #[
        ``Bcs.StoppedCharges.oracle_sound_joint,
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le]),
      (``RecursivePolygero.FiatShamir.TwoLevel.fixed_failure_le_iop, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.local_average,
        ``RecursivePolygero.FiatShamir.TwoLevel.sum_budget_query_le]),
      (``RecursivePolygero.Instances.FSCompletion81.certifiedBounds, #[
        ``RecursivePolygero.Instances.FSDefectSpectrum.actual_parent_mean_le,
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacity_mean_le,
        ``RecursivePolygero.FiatShamir.TwoLevel.query_joint_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.joint_whole_block_affine_bound,
        ``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed,
        ``RecursivePolygero.FiatShamir.TwoLevel.fixed_failure_le_iop,
        ``RecursivePolygero.Instances.FSDefect81.actual_iop_error]),
      (``RecursivePolygero.Instances.FSCompletion81.certifiedFailure_iop, #[
        ``RecursivePolygero.Instances.FSCompletion81.certifiedBounds,
        ``RecursivePolygero.Instances.FSCompletion81.checked]),
      (``RecursivePolygero.Instances.FSCompletion81.certifiedSoundness_iop, #[
        ``RecursivePolygero.Instances.FSCompletion81.certifiedFailure_iop,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_empty_iff])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`Bcs.UnseenCompletion, `Bcs.PairCompletion, `Bcs.StoppedCompletion,
      `polygero.Recursion.FSJointCompletion, `polygero.Instances.FSCompletion81].contains owner do
      continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
