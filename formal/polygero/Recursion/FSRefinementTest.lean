import polygero.Benchmarks.FSIntegerAffine
import polygero.Benchmarks.FSRetunedAffine
import polygero.Benchmarks.FSStoppedSpectrum
import polygero.Local.CapacityRigidity
import polygero.Recursion.FSStoppedCharges
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the strengthened actual FS certificates and the separate local
stopped-price lemmas. Numeric sensitivity is never used as a ROM bridge. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``CodingTheory.IntegerOccupancy.family_inequality, #[
        ``CodingTheory.IntegerOccupancy.occupancy_gap]),
      (``CodingTheory.IntegerOccupancy.uniformFamilyBound, #[
        ``CodingTheory.IntegerOccupancy.family_inequality]),
      (``RecursivePolygero.Benchmarks.FSIntegerAffine.certificate, #[
        ``CodingTheory.IntegerOccupancy.uniformFamilyBound,
        ``RecursivePolygero.HahnSystemCertificate.ofUniformFamilyBound]),
      (``RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedAffineFS, #[
        ``RecursivePolygero.Benchmarks.FSIntegerAffine.certificate,
        ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound]),
      (``RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedFS, #[
        ``RecursivePolygero.Benchmarks.FSIntegerAffine.certificate,
        ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound,
        ``RecursivePolygero.Benchmarks.FSIntegerAffine.absorb_rank]),
      (``RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedSoundness, #[
        ``RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedFS]),
      (``RecursivePolygero.Benchmarks.FSRetunedAffine.fixedCertifiedFS, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound,
        ``RecursivePolygero.Benchmarks.FSRetunedAffine.absorb_small_rate]),
      (``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.weightedExceptions_repeatPrice_mean_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.repeatPrice_sum_indicator_le,
        ``RecursivePolygero.ProfileAnalysis.systemExceptions_mean]),
      (``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.spectrum_layers_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.price_layers_le,
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.sum_price_le_of_tail_majorant]),
      (``RecursivePolygero.Benchmarks.FSStoppedSpectrum.fixed81_spectrum_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.spectrum_layers_le,
        ``RecursivePolygero.Benchmarks.FSStoppedSpectrum.actual_tail_card]),
      (``RecursivePolygero.Benchmarks.FSStoppedSpectrum.fixed81_parent_mean_le, #[
        ``RecursivePolygero.Benchmarks.FSStoppedSpectrum.fixed81_spectrum_le,
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le]),
      (``RecursivePolygero.ProfileAnalysis.assigned_payload_unique_of_capacity, #[
        ``RecursivePolygero.ProfileAnalysis.assigned_union_capacity_le,
        ``RecursivePolygero.ProfileAnalysis.payload_unique_of_good_overlap,
        ``RecursivePolygero.ProfileAnalysis.assigned_primary_unique]),
      (``RecursivePolygero.ProfileAnalysis.high_assigned_payload_unique_of_capacity, #[
        ``RecursivePolygero.ProfileAnalysis.assigned_payload_unique_of_capacity,
        ``RecursivePolygero.ProfileAnalysis.high_response_cutoff_le]),
      (``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le, #[
        ``RecursivePolygero.ProfileAnalysis.assignedExceptionQuery_conditional_le]),
      (``RecursivePolygero.FiatShamir.TwoLevel.failure_capacity_cover, #[
        ``RecursivePolygero.ProfileAnalysis.high_target_list_cover]),
      (``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound, #[
        ``Bcs.StoppedCharges.oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le]),
      (``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound_of_spectrum, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound,
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Algebra.Counting.IntegerOccupancy,
      `polygero.Local.StoppedSpectrum, `polygero.Local.CapacityRigidity,
      `polygero.Recursion.FSQueryCapacity, `polygero.Recursion.FSStoppedCharges,
      `polygero.Benchmarks.FSIntegerAffine,
      `polygero.Benchmarks.FSRetunedAffine, `polygero.Benchmarks.FSStoppedSpectrum].contains owner do
      continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
