import polygero.Benchmarks.FSNonuniformSpectrum
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Complete ownership audit for the nonuniform occupancy and exact
rational spectrum certificates. Arithmetic is checked by the kernel. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, deps) in #[
      (``CodingTheory.NonuniformOccupancy.sum_card_le, #[
        ``CodingTheory.NonuniformOccupancy.total_size]),
      (``RecursivePolygero.Benchmarks.FSNonuniformData.affine_majorants, #[
        ``RecursivePolygero.Benchmarks.FSNonuniformData.checked_ranges,
        ``RecursivePolygero.Benchmarks.FSNonuniformData.checked]),
      (``RecursivePolygero.Benchmarks.FSNonuniformSpectrum.actual_spectrum_le, #[
        ``RecursivePolygero.Local.ReducedSystems.capacity_witness,
        ``RecursivePolygero.ProfileAnalysis.highSystems_card_le]),
      (``RecursivePolygero.Benchmarks.FSNonuniformSpectrum.query_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound_of_spectrum,
        ``RecursivePolygero.Benchmarks.FSNonuniformSpectrum.actual_spectrum_premise])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in deps do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Algebra.Counting.NonuniformOccupancy,
      `polygero.Benchmarks.FSNonuniformData,
      `polygero.Benchmarks.FSNonuniformSpectrum].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
