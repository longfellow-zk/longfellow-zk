import polygero.Benchmarks.FSDefectSpectrum
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! All-owner and actual-dependency audit for the clean 126-bit parent rate. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``RecursivePolygero.Benchmarks.FSDefectSpectrum.actual_low_defect_spectrum_le, #[
        ``RecursivePolygero.ProfileAnalysis.low_defect_core_intersection_le,
        ``RecursivePolygero.ProfileAnalysis.capacity_add_defect_le_core_add_masks]),
      (``RecursivePolygero.Benchmarks.FSDefectSpectrum.actual_parent_mean_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le_defect_split,
        ``RecursivePolygero.Benchmarks.FSDefectSpectrum.actual_low_defect_spectrum_le,
        ``RecursivePolygero.Benchmarks.FSDefectData.checked]),
      (``RecursivePolygero.Benchmarks.FSDefectSpectrum.query_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound,
        ``RecursivePolygero.Benchmarks.FSDefectSpectrum.actual_parent_mean_le])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Benchmarks.FSDefectData,
      `polygero.Benchmarks.FSDefectSpectrum].contains owner do
      continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
