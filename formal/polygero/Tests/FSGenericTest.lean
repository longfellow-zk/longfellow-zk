import polygero.Recursion.FiatShamir
import Lean.Util.CollectAxioms

/-! Regression boundary: the reusable ROM and capacity-C proof stack must
compile without importing any numerical instance or benchmark module. -/
open Lean Elab Command

#guard_msgs (drop info) in
#check RecursivePolygero.ProfileAnalysis.split_budget_joint_le
#guard_msgs (drop info) in
#check RecursivePolygero.FiatShamir.MerkleFS.SplitChild.oracle_sound_joint_completion
#guard_msgs (drop info) in
#check RecursivePolygero.FiatShamir.MerkleFS.extraction_failure_bound_of_blocks

run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if moduleName.toString.startsWith "polygero.Instances." ||
        moduleName.toString.startsWith "polygero.Benchmarks." then
      throwError "Generic proof stack imports parameter module {moduleName}"
  for (name,info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless #[`polygero.Local.SplitChildPrice,
      `polygero.Recursion.FSRootAnalysis, `polygero.Recursion.FSRootComposition,
      `polygero.Recursion.FSRootSoundness, `polygero.Recursion.FSRemainingBudget,
      `polygero.Recursion.FSRootSplitChild, `polygero.Recursion.FSRootChildCompletion].contains owner do continue
    if info.isAxiom then throwError "Unexpected axiom {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
