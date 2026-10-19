import polygero.Recursion.FSGrindingConcrete
import polygero.Recursion.FSGrindingLowerBound
import polygero.Benchmarks.FSGrinding
import polygero.Benchmarks.FSGrindingInstance
import polygero.Benchmarks.FSGrindingObstruction
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the actual algebra, physical commitment family, bounded fresh
ROM tree, exact search probability and standard recursive-FS failure
reduction. The public grinding endpoints and large numerical comparisons
must use ordinary kernel axioms only. The full module audit is also part
of the project-wide Polygero API check. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``RecursivePolygero.FiatShamir.TwoLevel.grinding_query_injective, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.varied_wire_query_injective]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingProof_accepts, #[
        ``RecursivePolygero.ProfileAnalysis.GrindingAlgebra.packed_child_satisfies,
        ``RecursivePolygero.ProfileAnalysis.HonestCompletion.varied_verify_avoiding]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingFinish_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingProof_accepts]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingChildren_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingFinish_sound]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_sound, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingChildren_sound]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_failure, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.failure_of_accepts_of_false]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingChildren_fresh, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grinding_query_injective,
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingFinish_fresh]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_fresh, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_fresh_from_roots]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_probability, #[
        ``Bcs.TotalOracle.FreshSearch.totalOracle_eq_iid,
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_fresh,
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_iid]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_lower, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_probability,
        ``RecursivePolygero.FiatShamir.TwoLevel.grinding_product_lower]),
      (``RecursivePolygero.FiatShamir.TwoLevel.grindingAdversary_failure_lower, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_lower,
        ``RecursivePolygero.FiatShamir.TwoLevel.grinding_success_le_failure]),
      (``RecursivePolygero.FiatShamir.TwoLevel.geometryRoots_injective, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.mixtureRoots_injective]),
      (``RecursivePolygero.FiatShamir.TwoLevel.geometryPrepare_good_mean, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.mixturePrepare_good_mean,
        ``RecursivePolygero.ProfileAnalysis.GrindingGeometry.region_query_mean]),
      (``RecursivePolygero.FiatShamir.TwoLevel.geometryPrepare_root_mean, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.three_regions_eligible_mean,
        ``RecursivePolygero.FiatShamir.TwoLevel.geometryPrepare_root_isSome]),
      (``RecursivePolygero.FiatShamir.TwoLevel.geometry_exists_failure_tree, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.grindingAdversary_failure_lower,
        ``RecursivePolygero.FiatShamir.TwoLevel.geometryPrepare_root_mean_ne_none,
        ``RecursivePolygero.FiatShamir.TwoLevel.geometryPrepare_good_mean,
        ``RecursivePolygero.FiatShamir.TwoLevel.geometryRoots_injective]),
      (``RecursivePolygero.Benchmarks.FSGrindingInstance.field128_card, #[
        ``GaloisField.card]),
      (``RecursivePolygero.Benchmarks.FSGrindingInstance.concreteDomain, #[
        ``RecursivePolygero.Benchmarks.FSGrindingInstance.domain,
        ``RecursivePolygero.Benchmarks.FSGrindingInstance.field128_card]),
      (``RecursivePolygero.Benchmarks.FSGrindingObstruction.exists_no_loss_violation, #[
        ``RecursivePolygero.FiatShamir.TwoLevel.geometry_exists_failure_tree,
        ``RecursivePolygero.Benchmarks.FSTwoLevel.certificate,
        ``RecursivePolygero.Benchmarks.FSGrinding.checked]),
      (``RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_violation, #[
        ``RecursivePolygero.Benchmarks.FSGrindingObstruction.exists_no_loss_violation,
        ``RecursivePolygero.Benchmarks.FSGrindingInstance.field128_card,
        ``RecursivePolygero.Benchmarks.FSGrindingInstance.concreteDomain]),
      (``RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_soundness_violation, #[
        ``RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_violation,
        ``Bcs.FiniteProbability.density_mono])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for name in #[
      ``RecursivePolygero.ProfileAnalysis.GrindingAlgebra.mixture_accepts,
      ``RecursivePolygero.ProfileAnalysis.GrindingAlgebra.contradictoryStatement_false,
      ``RecursivePolygero.ProfileAnalysis.HonestCompletion.varied_verify_avoiding,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingProof_accepts,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_sound,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_failure,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_fresh,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_probability,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingSearch_success_lower,
      ``RecursivePolygero.FiatShamir.TwoLevel.grinding_success_le_failure,
      ``RecursivePolygero.FiatShamir.TwoLevel.grindingAdversary_failure_lower,
      ``RecursivePolygero.FiatShamir.TwoLevel.geometry_exists_failure_tree,
      ``RecursivePolygero.Benchmarks.FSGrinding.checked,
      ``RecursivePolygero.Benchmarks.FSGrinding.original70_checked,
      ``RecursivePolygero.Benchmarks.FSGrindingInstance.packing_surjective,
      ``RecursivePolygero.Benchmarks.FSGrindingInstance.field128_card,
      ``RecursivePolygero.Benchmarks.FSGrindingInstance.concrete_geometry,
      ``RecursivePolygero.Benchmarks.FSGrindingInstance.concrete_retuned_geometry,
      ``RecursivePolygero.Benchmarks.FSGrindingObstruction.exists_no_loss_violation,
      ``RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_violation,
      ``RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_soundness_violation] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
