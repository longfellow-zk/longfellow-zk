import polygero.Instances.FSBaselinePrice
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Dependency and axiom audit for the actual list-six-baseline certificate. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``RecursivePolygero.Instances.FSBaselinePrice.actual_spectrum_le, #[
        ``RecursivePolygero.ProfileAnalysis.StoppedSpectrum.spectrum_layers_le,
        ``RecursivePolygero.Instances.FSStoppedSpectrum.actual_tail_card]),
      (``RecursivePolygero.Instances.FSBaselinePrice.actual_spectrum_premise, #[
        ``RecursivePolygero.Instances.FSBaselinePrice.actual_spectrum_le,
        ``RecursivePolygero.Instances.FSBaselinePrice.checked]),
      (``RecursivePolygero.Instances.FSBaselinePrice.query_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound_of_spectrum,
        ``RecursivePolygero.Instances.FSBaselinePrice.actual_spectrum_premise])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `polygero.Instances.FSBaselinePrice do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
