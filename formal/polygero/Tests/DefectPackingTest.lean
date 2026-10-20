import polygero.Local.DefectPacking
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Actual dependency and complete module trust audit for defect splitting. -/
open Lean Elab Command RecursivePolygero.ProfileAnalysis
open RecursivePolygero.ProfileAnalysis.StoppedSpectrum

run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``capacity_add_defect_le_core_add_masks, #[
        ``RecursivePolygero.Local.ReducedSystems.capacity_witness,
        ``RecursivePolygero.Local.PolynomialClosure.canonical_core,
        ``RecursivePolygero.Local.PolynomialClosure.closure_geometry]),
      (``low_defect_core_intersection_le, #[
        ``RecursivePolygero.Local.PolynomialClosure.core_union_mds,
        ``RecursivePolygero.Local.ConsistencyClosure.solutions_eq_of_rank_eq]),
      (``fixed_low_defect_capacity_systems_card_le_four, #[
        ``low_defect_capacity_systems_card_le,
        ``CodingTheory.IntegerOccupancy.uniformFamilyBound]),
      (``low_defect_capacity_sum_le, #[
        ``capacity_add_defect_le_core_add_masks,
        ``low_defect_core_intersection_le]),
      (``systemConsistency_mean_le_inv_sq_of_defect, #[
        ``RecursivePolygero.Local.Affine.consistent_card_mul_field_pow_le]),
      (``systemExceptions_mean_le_inv_sq_of_defect, #[
        ``system_not_full_of_high_defect,
        ``systemConsistency_mean_le_inv_sq_of_defect]),
      (``weightedExceptions_repeatPrice_mean_le_defect_split, #[
        ``repeatPrice_sum_indicator_le,
        ``systemExceptions_mean_le_inv_sq_of_defect,
        ``highSystems_card_le]),
      (``conditionalCapacity_repeatPrice_mean_le_defect_split, #[
        ``rank_bad_mean,
        ``baseline_weightedExceptions_repeatPrice_mean_le_defect_split])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `polygero.Local.DefectPacking do continue
    if info.isAxiom then throwError "Unexpected defect-packing axiom: {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
