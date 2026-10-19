import Lfzk.PolygeroStructure
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! The LFZK circuit slice is checked against the actual circuit semantics,
state transitions, honest arithmetization and standard tableau encoding. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``Lfzk.PolygeroStructure.Circuit.false_for_every_witness, #[
        ``Lfzk.Arith.QuadCircuit.Satisfied,
        ``Lfzk.Arith.QuadCircuit.wires_lt]),
      (``Lfzk.PolygeroStructure.Circuit.actual_prefix_reaches, #[
        ``Lfzk.RbrZkLongfellow.zkInputBind,
        ``Lfzk.RbrZkLongfellow.zkInit,
        ``Lfzk.RbrZkLongfellow.inputSystem]),
      (``Lfzk.PolygeroStructure.Circuit.prefix_stays_wrong, #[
        ``Lfzk.RbrZkLongfellow.ZkWrong,
        ``Lfzk.PolygeroStructure.Circuit.honest_init_sum,
        ``Lfzk.PolygeroStructure.Circuit.actual_prefix_reaches,
        ``Lfzk.PolygeroStructure.Circuit.no_candidate_satisfies]),
      (``Lfzk.PolygeroStructure.Circuit.encoded_copy_and_product, #[
        ``Lfzk.Encode.satisfies_encodeLig,
        ``Lfzk.PolygeroStructure.Circuit.product]),
      (``Lfzk.PolygeroStructure.Circuit.encoded_residuals, #[
        ``Lfzk.PolygeroStructure.encoded_row_residual,
        ``Lfzk.PolygeroStructure.Circuit.layer_residual,
        ``Lfzk.PolygeroStructure.Circuit.input_residual]),
      (``Lfzk.PolygeroStructure.Circuit.distinct_exception_lines, #[
        ``Lfzk.PolygeroStructure.exception_lines_intersect_only_zero])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `Lfzk.PolygeroStructure do continue
    if info.isAxiom then throwError "Unexpected circuit-slice axiom: {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
