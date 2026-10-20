import polygero.Instances.FSShiftedCompiled81
import polygero.Instances.FSFiniteHorizon81
import polygero.Instances.FSCoreStoppingAudit
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the actual-core refinement through the verifier and both BCS
errors. Importing an earlier theorem is insufficient: the improved bound
must depend on the refined algebra and its semantic query cover. -/
open Lean Elab Command
private partial def shiftedDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then shiftedDependencies env rest seen else
      let deps := match env.find? name with
        | some info => info.getUsedConstantsAsSet.toList
        | none => []
      shiftedDependencies env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``RecursivePolygero.Instances.FSShifted81.analysis_exists, #[
        ``RecursivePolygero.Instances.FSShiftedSpectrum.actual_parent_mean_le,
        ``RecursivePolygero.ProfileAnalysis.ShiftedSpectrum.baseline_le_price,
        ``RecursivePolygero.ProfileAnalysis.ShiftedSpectrum.price_sum_le,
        ``RecursivePolygero.ProfileAnalysis.exception_outside_mean_le]),
      (``RecursivePolygero.Instances.FSShiftedCompiled81.certified_comparisons, #[
        ``RecursivePolygero.Instances.FSShifted81.analysis_exists,
        ``RecursivePolygero.Instances.FSCoreCompiled81.extraction_failure_bound_at,
        ``RecursivePolygero.Instances.FSMerkleCore81.root_failure_bound_at,
        ``RecursivePolygero.FiatShamir.MerkleFS.Capacity.queryRisk_pair_mean,
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le_core,
        ``Bcs.TotalOracleCommit.Setup.merkle_bad_ratio_le,
        ``RecursivePolygero.FiatShamir.MerkleFS.failure_of_explains,
        ``RecursivePolygero.Instances.FSCoreCompiled81.no_merkle_failure_bound,
        ``RecursivePolygero.Instances.FSShiftedCompiledData.checked]),
      (``RecursivePolygero.Instances.FSShiftedCompiled81.false_statement_bound, #[
        ``RecursivePolygero.Instances.FSShiftedCompiled81.certified_comparisons,
        ``RecursivePolygero.FiatShamir.MerkleFS.extractor_none_of_false]),
      (``RecursivePolygero.Instances.FSFiniteHorizon81.ordered_four_core_bound, #[
        ``Bcs.StoppedPotential.renewalSearch_le_pairs,
        ``RecursivePolygero.Instances.FSFiniteHorizon81.checked]),
      (``RecursivePolygero.Instances.FSFiniteHorizon81.immediate_four_core_bound, #[
        ``Bcs.StoppedPotential.renewalImmediate_le_pairs,
        ``RecursivePolygero.Instances.FSFiniteHorizon81.checked])] do
    let some _ := env.find? name | throwError "Missing theorem {name}"
    let used := shiftedDependencies env [name]
    for dep in deps do
      unless used.contains dep do throwError "{name} omits actual dependency {dep}"
  let globalProof := shiftedDependencies env
    [``RecursivePolygero.Instances.FSShiftedCompiled81.certified_comparisons]
  for abstractBound in #[
      ``RecursivePolygero.Instances.FSFiniteHorizon81.ordered_four_core_bound,
      ``RecursivePolygero.Instances.FSFiniteHorizon81.immediate_four_core_bound] do
    if globalProof.contains abstractBound then
      throwError "The abstract renewal bound must not be assumed for the actual ROM"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Local.ShiftedPrice, `polygero.Local.ShiftedEnvelope,
      `polygero.Instances.FSShiftedData, `polygero.Instances.FSShiftedSpectrum,
      `polygero.Instances.FSShifted81, `polygero.Instances.FSShiftedCompiled81,
      `polygero.Instances.FSShiftedCompiledData, `Bcs.FiniteRenewal,
      `polygero.Instances.FSFiniteHorizon81].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
