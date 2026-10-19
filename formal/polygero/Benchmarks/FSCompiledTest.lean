import polygero.Benchmarks.FSCompiledHeadline
import polygero.Benchmarks.FSGeometryAudit
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit every owned declaration and the actual end-to-end dependency path. -/
open Lean Elab Command
private partial def compiledDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then compiledDependencies env rest seen else
      let deps := match env.find? name with
        | some info => info.getUsedConstantsAsSet.toList
        | none => []
      compiledDependencies env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  for (name,deps) in #[
      (``Bcs.TotalOracleCommit.Setup.ctxAt_off_finset, #[
        ``Bcs.TotalOracle.invariant_finset, ``Bcs.TotalOracleCommit.Setup.ctxAt_off]),
      (``RecursivePolygero.FiatShamir.MerkleFS.context, #[
        ``Bcs.TotalOracleCommit.Setup.ctxAt_off_finset,
        ``RecursivePolygero.FiatShamir.MerkleFS.parentSetup,
        ``RecursivePolygero.FiatShamir.MerkleFS.childSetup]),
      (``RecursivePolygero.FiatShamir.MerkleFS.query_oracle_sound, #[
        ``Bcs.AffineBlock.oracle_sound_of_contextual_pair_completion,
        ``RecursivePolygero.FiatShamir.MerkleFS.queryRisk_pair_mean]),
      (``RecursivePolygero.FiatShamir.MerkleFS.child_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.terminal_block_oracle_sound,
        ``RecursivePolygero.FiatShamir.TwoLevel.wholeChildBlock_pay]),
      (``RecursivePolygero.Benchmarks.FSMerkle81.analysis_exists, #[
        ``RecursivePolygero.Benchmarks.FSWholeBlock81.certificate_with_cutoff,
        ``RecursivePolygero.Benchmarks.FSBaselineAwareSpectrum.actual_parent_mean_le,
        ``RecursivePolygero.ProfileAnalysis.fixed_rigidBlockCharge_mean_le]),
      (``RecursivePolygero.Benchmarks.FSMerkle81.root_oracle_sound, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.query_oracle_sound,
        ``RecursivePolygero.FiatShamir.MerkleFS.child_oracle_sound,
        ``Bcs.AffineBlock.oracle_parallel_certificate]),
      (``RecursivePolygero.FiatShamir.MerkleFS.accepts_of_explains, #[
        ``RecursivePolygero.FiatShamir.MerkleFS.opened_eq,
        ``RecursivePolygero.FiatShamir.MerkleFS.child_output_eq]),
      (``RecursivePolygero.Benchmarks.FSCompiled81.extraction_failure_bound, #[
        ``RecursivePolygero.Benchmarks.FSMerkle81.root_failure_bound,
        ``Bcs.TotalOracleCommit.Setup.merkle_bad_ratio_le,
        ``RecursivePolygero.FiatShamir.MerkleFS.failure_of_explains,
        ``RecursivePolygero.Benchmarks.FSCompiled81.check_parent,
        ``RecursivePolygero.Benchmarks.FSCompiled81.check_child]),
      (``RecursivePolygero.Benchmarks.FSCompiled81.certified_bound, #[
        ``RecursivePolygero.Benchmarks.FSMerkle81.analysis_exists,
        ``RecursivePolygero.Benchmarks.FSCompiled81.extraction_failure_bound]),
      (``RecursivePolygero.Benchmarks.FSCompiled81.comparison_bound, #[
        ``RecursivePolygero.Benchmarks.FSCompiled81.extraction_failure_bound,
        ``RecursivePolygero.Benchmarks.FSCompiledData.comparison,
        ``RecursivePolygero.Benchmarks.FSCompiled81.zero_work_failure_bound]),
      (``RecursivePolygero.Benchmarks.FSCompiled81.certified_comparisons, #[
        ``RecursivePolygero.Benchmarks.FSMerkle81.analysis_exists,
        ``RecursivePolygero.Benchmarks.FSCompiled81.comparison_bound,
        ``RecursivePolygero.Benchmarks.FSCompiledData.checked]),
      (``RecursivePolygero.Benchmarks.FSCompiled81.false_statement_bound, #[
        ``RecursivePolygero.Benchmarks.FSCompiled81.certified_comparisons,
        ``RecursivePolygero.Benchmarks.FSCompiled81.extractor_none_of_false])] do
    let some _ := env.find? name | throwError "Missing theorem {name}"
    let used := compiledDependencies env [name]
    for dep in deps do
      unless used.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`Bcs.ContextualCompletion,`Bcs.CutContext,`Bcs.CommitReplay,
      `polygero.Recursion.FSRootModel,`polygero.Recursion.FSRootQuery,
      `polygero.Recursion.FSRootTerminal,`polygero.Recursion.FSRootCommit,
      `polygero.Recursion.FSRootBridge,`polygero.Recursion.FSRootCodec,
      `polygero.Benchmarks.FSMerkle81,`polygero.Benchmarks.FSCompiled81,
      `polygero.Benchmarks.FSCompiledData,`polygero.Benchmarks.FSCompiledCorollaries,
      `polygero.Benchmarks.FSCompiledHeadline].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom declaration {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
