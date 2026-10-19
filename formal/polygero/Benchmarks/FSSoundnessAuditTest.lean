import polygero.Benchmarks.FSBaselineAware81
import polygero.Benchmarks.FSStoppingAudit
import polygero.Benchmarks.FSGeometryAudit
import polygero.Local.CoreOnlyCapacity
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Check that the audit and refinement use actual protocol theorems,
and that every owned declaration has only the three standard axioms. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``RecursivePolygero.ProfileAnalysis.outside_column_defect_lt, #[
        ``RecursivePolygero.Local.ConsistencyClosure.subset_closure_of_rank_eq,
        ``RecursivePolygero.Local.PolynomialClosure.joint_rank]),
      (``RecursivePolygero.ProfileAnalysis.outside_column_consistency_mean_le_inv_sq, #[
        ``RecursivePolygero.ProfileAnalysis.outside_column_defect_lt,
        ``RecursivePolygero.Local.Affine.consistent_card_mul_field_pow_le]),
      (``RecursivePolygero.ProfileAnalysis.assigned_query_union_mean_le_core, #[
        ``RecursivePolygero.ProfileAnalysis.assigned_good_subset_core_of_not_outside,
        ``RecursivePolygero.Local.Polygero.verify_openOracle_iff]),
      (``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le_effective, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.repeatPrice_baseline_le_effective,
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.weightedExceptions_price_mean_le_defect_split]),
      (``RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum.actual_parent_mean_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le_effective,
        ``RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum.actual_low_defect_spectrum_le]),
      (``RecursivePolygero.Benchmarks.FSIOPReference81.interactive_failure_le_strongIOP, #[
        ``RecursivePolygero.Benchmarks.FSIOPReference81.certificate,
        ``RecursivePolygero.Benchmarks.FSIOPReference81.twoProof_run_independent,
        ``RecursivePolygero.Protocol.HahnProfileProof.extraction_failure_le]),
      (``RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedBounds, #[
        ``RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum.actual_parent_mean_le,
        ``RecursivePolygero.FiatShamir.TwoLevel.query_joint_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed,
        ``RecursivePolygero.FiatShamir.TwoLevel.joint_whole_block_affine_bound,
        ``RecursivePolygero.Benchmarks.FSIOPReference81.fixed_failure_le_strongIOP]),
      (``RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedSoundness_workingIOP, #[
        ``RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedSoundness_comparison,
        ``RecursivePolygero.Benchmarks.FSBaselineAwareData.checked]),
      (``RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedSoundness_strongIOP, #[
        ``RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedSoundness_comparison,
        ``RecursivePolygero.Benchmarks.FSBaselineAware81.checked_strong])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Local.BaselineAwarePrice,
      `polygero.Benchmarks.FSBaselineAwareData, `polygero.Benchmarks.FSBaselineAwareSpectrum,
      `polygero.Benchmarks.FSIOPReference81, `polygero.Benchmarks.FSBaselineAware81,
      `polygero.Benchmarks.FSStoppingAudit, `polygero.Benchmarks.FSGeometryAudit,
      `polygero.Local.CoreOnlyCapacity].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
