import polygero.Recursion.FSRemainingBudget
import polygero.Instances.FSJointChildCompiled81
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit actual cached sampling, conditional terminal completion, joint
child loads and both unchanged BCS errors. -/
open Lean Elab Command
open Bcs.TotalOracle.CachedPotential Bcs.TotalOracle.Footprint Merkle.RandomOracle

private def repeatQuery : Tree Unit Bool Bool 2 :=
  .query () (fun a => .query () (fun b => .done (a != b)))

/-- A repeated lookup cannot supply a second independent random answer. -/
private theorem cached_repeat_regression :
    expectation (fun b _ => if b then 1 else 0) repeatQuery (fun _ => none) = 0 := by
  rw [← totalOracle_eq_expectation]
  simp [conditional,repeatQuery]

private partial def cachedDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then cachedDependencies env rest seen else
      let deps := match env.find? name with
        | some info => info.getUsedConstantsAsSet.toList
        | none => []
      cachedDependencies env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``Bcs.TotalOracle.CachedPotential.totalOracle_eq_expectation, #[
        ``Bcs.TotalOracle.Footprint.average_resample,
        ``Bcs.TotalOracle.sum_coord_mul_rat]),
      (``RecursivePolygero.FiatShamir.MerkleFS.RemainingBudget.extraction_failure_bound, #[
        ``Bcs.TotalOracle.CachedPotential.totalOracle_le_timePotential,
        ``Bcs.TotalOracle.CachedPotential.expectation_le_timePotential,
        ``RecursivePolygero.FiatShamir.MerkleFS.failure_of_explains,
        ``Bcs.TotalOracleCommit.Setup.merkle_bad_ratio_le]),
      (``RecursivePolygero.Instances.FSJointChild81.certified_child, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.SplitChild.oracle_sound_joint_completion,
        ``RecursivePolygero.FiatShamir.MerkleFS.SplitChild.fresh_pair_mean,
        ``RecursivePolygero.ProfileAnalysis.excluded_target_response_mean_le,
        ``RecursivePolygero.ProfileAnalysis.fixed_rigid_excess_add_nonrigid_count_le_two,
        ``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlock_pay,
        ``Bcs.AffineBlock.oracle_sound_of_contextual_footprint_completion]),
      (``RecursivePolygero.Instances.FSJointChildCompiled81.certified_bound, #[
        ``RecursivePolygero.Instances.FSShifted81.analysis_exists_with_child_data,
        ``RecursivePolygero.Instances.FSJointChild81.child_oracle_sound_joint,
        ``RecursivePolygero.Instances.FSJointChildCompiled81.extraction_failure_bound_of_parent]),
      (``RecursivePolygero.Instances.FSJointChildCompiled81.extraction_failure_bound_of_parent, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.root_oracle_sound_of_blocks,
        ``RecursivePolygero.Instances.FSJointChild81.capacity_le_two,
        ``Bcs.AffineBlock.oracle_parallel_certificate,
        ``Bcs.TotalOracleCommit.Setup.merkle_bad_ratio_le,
        ``RecursivePolygero.FiatShamir.MerkleFS.accepts_of_explains])] do
    let some _ := env.find? name | throwError "Missing theorem {name}"
    let used := cachedDependencies env [name]
    for dep in deps do
      unless used.contains dep do throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`Bcs.CachedPotential, `Bcs.ContextualFootprints,
      `polygero.Local.SplitChildPrice, `polygero.Local.ExcludedTargets,
      `polygero.Recursion.FSRootChildFresh, `polygero.Recursion.FSRootChildCompletion,
      `polygero.Recursion.FSRootSplitChild,
      `polygero.Recursion.FSRemainingBudget, `polygero.Recursion.FSRootSoundness,
      `polygero.Recursion.FSRootComposition, `polygero.Recursion.FSRootAnalysis, `polygero.Instances.FSJointChild81,
      `polygero.Instances.FSJointChildCompiled81].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
