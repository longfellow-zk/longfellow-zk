import Lfzk.Fork.CircuitHeadline
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Audit the concrete forked transcript/Merkle bridge, including its
circuit-level false-statement endpoint and inherited numerical trust. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  for (name, required) in #[
      (``Lfzk.Fork.Transcript.setup2, #[``Lfzk.Fork.Transcript.hash2]),
      (``Lfzk.Fork.PotentialFS.twoFieldHybrid_fs_extraction_outside, #[
        ``Bcs.TotalOracleCommit.Setup.extraction_failure_ratio_le_two_verifier_potential,
        ``Lfzk.Fork.Transcript.setup2_hashInput_injective]),
      (``Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le, #[
        ``Lfzk.Fork.PotentialFS.twoFieldHybrid_fs_extraction_outside,
        ``Lfzk.Fork.JointBound.hash1_cut_failure_joint_le,
        ``Lfzk.Fork.HybridPath.flatEvent_pays_outside_terminal]),
      (``Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le_116_circuit_typed, #[
        ``Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le_116_mac_typed]),
      (``Lfzk.Fork.HybridFS.falseStatement_hybrid_fs_ratio_le_116_circuit_typed, #[
        ``Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le_116_circuit_typed])] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    for dep in required do
      unless info.getUsedConstantsAsSet.contains dep do
        throwError "{name} omits actual dependency {dep}"
  for name in #[
      ``Lfzk.Fork.Transcript.hash2_side1_independent,
      ``Lfzk.Fork.Transcript.hash2_side2_independent,
      ``Lfzk.Fork.Transcript.setup2_hashInput_injective,
      ``Lfzk.Fork.PotentialFS.twoFieldHybrid_fs_extraction_outside] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
  let inherited ← collectAxioms
    ``Lfzk.V1StrongV7Hash1HybridFS.falseStatement_hybrid_fs_ratio_le_116_circuit_typed
  for name in #[
      ``Lfzk.Fork.HybridFS.flatEvent_hybrid_fs_ratio_le_116_circuit_typed,
      ``Lfzk.Fork.HybridFS.falseStatement_hybrid_fs_ratio_le_116_circuit_typed] do
    let some info := env.find? name | throwError "Missing theorem {name}"
    unless info.type.getUsedConstants.contains ``Lfzk.Fork.Transcript.setup2 do
      throwError "{name} does not state the forked setup"
    for ax in ← collectAxioms name do
      if ax == ``sorryAx then throwError "Unfinished proof in {name}"
      unless inherited.contains ax do
        throwError "New trust assumption {ax} in {name}"
