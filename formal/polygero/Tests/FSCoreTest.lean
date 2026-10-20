import polygero.Instances.FSCoreCompiled81
import polygero.Instances.FSCoreStoppingAudit
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the actual-core refinement through the verifier and both BCS
errors. Importing an earlier theorem is insufficient: the improved bound
must depend on the refined algebra and its semantic query cover. -/
open Lean Elab Command
private partial def coreDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then coreDependencies env rest seen else
      let deps := match env.find? name with
        | some info => info.getUsedConstantsAsSet.toList
        | none => []
      coreDependencies env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``RecursivePolygero.ProfileAnalysis.exception_outside_mean_le, #[
        ``RecursivePolygero.ProfileAnalysis.outsidePrimary_mean_le,
        ``RecursivePolygero.ProfileAnalysis.outsidePrimary_mean_le_inv]),
      (``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le_core, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le_of_exception_bound,
        ``RecursivePolygero.ProfileAnalysis.assigned_query_union_mean_le_core]),
      (``RecursivePolygero.Instances.FSMerkleCore81.analysis_exists, #[
        ``RecursivePolygero.Instances.FSCoreSpectrum.actual_parent_mean_le,
        ``RecursivePolygero.ProfileAnalysis.exception_outside_mean_le,
        ``RecursivePolygero.ProfileAnalysis.fixed_rigidBlockCharge_mean_le]),
      (``RecursivePolygero.Instances.FSMerkleCore81.root_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.Capacity.queryRisk_pair_mean,
        ``RecursivePolygero.FiatShamir.TwoLevel.queryCapacityRisk_mean_le_core,
        ``RecursivePolygero.FiatShamir.MerkleFS.child_oracle_sound,
        ``Bcs.AffineBlock.oracle_parallel_certificate]),
      (``RecursivePolygero.Instances.FSCoreCompiled81.extraction_failure_bound, #[
        ``RecursivePolygero.Instances.FSMerkleCore81.root_failure_bound_at,
        ``Bcs.TotalOracleCommit.Setup.merkle_bad_ratio_le,
        ``RecursivePolygero.FiatShamir.MerkleFS.failure_of_explains,
        ``RecursivePolygero.FiatShamir.MerkleFS.check_parent,
        ``RecursivePolygero.FiatShamir.MerkleFS.check_child]),
      (``RecursivePolygero.Instances.FSCoreCompiled81.certified_comparisons, #[
        ``RecursivePolygero.Instances.FSMerkleCore81.analysis_exists,
        ``RecursivePolygero.Instances.FSCoreCompiled81.extraction_failure_bound,
        ``RecursivePolygero.Instances.FSCoreCompiled81.no_merkle_failure_bound,
        ``RecursivePolygero.Instances.FSCoreCompiledData.comparison,
        ``RecursivePolygero.Instances.FSCoreCompiledData.checked]),
      (``RecursivePolygero.Instances.FSCoreCompiled81.false_statement_bound, #[
        ``RecursivePolygero.Instances.FSCoreCompiled81.certified_comparisons,
        ``RecursivePolygero.FiatShamir.MerkleFS.extractor_none_of_false])] do
    let some _ := env.find? name | throwError "Missing theorem {name}"
    let used := coreDependencies env [name]
    for dep in deps do
      unless used.contains dep do throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Local.CoreEnvelope, `polygero.Recursion.FSQueryCapacity,
      `polygero.Recursion.FSCoreQuery, `polygero.Recursion.FSRootCapacity,
      `polygero.Instances.FSCoreData, `polygero.Instances.FSCoreSpectrum,
      `polygero.Instances.FSMerkleCore81, `polygero.Instances.FSCoreCompiled81,
      `polygero.Instances.FSCoreCompiledData,
      `polygero.Instances.FSCoreStoppingAudit].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
