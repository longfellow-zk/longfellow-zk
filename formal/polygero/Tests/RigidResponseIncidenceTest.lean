import polygero.Local.RigidResponseIncidence
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Dependency and axiom audit for the actual capacity-rigid adapter. -/
open Lean Elab Command RecursivePolygero.ProfileAnalysis

run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``high_assigned_payload_unique_of_rigid, #[
        ``assigned_payload_unique,
        ``high_assigned_payload_unique_of_capacity]),
      (``rigid_response_excess_le, #[
        ``high_assigned_payload_unique_of_rigid,
        ``assigned_response_fraction_le]),
      (``responseIncidence_le_localIncidence_of_rigid_cover, #[
        ``rigid_response_excess_le_of_cover]),
      (``responseIncidence_mean_of_rigid_cover, #[
        ``responseIncidence_le_localIncidence_of_rigid_cover,
        ``localIncidence_mean_of_hahn]),
      (``high_target_covered_or_nonrigid, #[
        ``high_target_response_cases,
        ``assigned_response_fraction_le]),
      (``nonrigidException_mean_le, #[``systemExceptions_mean]),
      (``fixed_nonrigidException_mean_le_two, #[
        ``nonrigidException_mean_le,
        ``fixed_nonrigid_systems_card_le_two]),
      (``responseIncidence_excess_mean_of_rigid_cover, #[
        ``responseIncidence_mean_of_rigid_cover]),
      (``fixed_two_nonrigid_no_high_rigid, #[``three_capacities_le]),
      (``fixed_rigid_excess_add_nonrigid_count_le_two, #[
        ``fixed_two_nonrigid_no_high_rigid, ``systemCap_excess_of_hahn]),
      (``fixed_rigidExceptionExcess_mean_le_two, #[
        ``rigidExceptionExcess_mean_le,
        ``fixed_rigid_excess_add_nonrigid_count_le_two]),
      (``responseIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge, #[
        ``responseIncidence_le_localIncidence_of_rigid_cover,
        ``localIncidence_sub_threshold_add_nonrigid_le_rigidBlockCharge]),
      (``fixed_rigidBlockCharge_mean_le, #[
        ``rank_bad_mean, ``systemCap_excess_of_hahn,
        ``fixed_rigidExceptionExcess_mean_le_two])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `polygero.Local.RigidResponseIncidence do continue
    if info.isAxiom then throwError "Unexpected rigid-response axiom: {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
