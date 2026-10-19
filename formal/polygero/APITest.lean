import polygero
import Bcs.StoppedPotentialTest
import polygero.Recursion.FSTransferTest
import polygero.Recursion.FSGrindingTest
import polygero.Recursion.FSRefinementTest
import polygero.Local.RigidResponseIncidenceTest
import polygero.Recursion.FSTerminalBlockTest
import polygero.Benchmarks.FSBaselinePriceTest
import polygero.Benchmarks.FSNonuniformSpectrumTest
import polygero.Benchmarks.FSWholeBlock81Test
import polygero.Local.DefectPackingTest
import polygero.Recursion.FSDefectSpectrumTest
import polygero.Benchmarks.FSDefect81Test
import polygero.Benchmarks.FSCompletion81Test
import polygero.Benchmarks.FSSoundnessAuditTest
import polygero.Benchmarks.FSCompiledTest
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Public recursive extraction and soundness endpoints. -/
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.twoLevel_incidence_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.twoLevel_fs_transfer
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.twoLevel_fs_transfer_of_fanout
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.failure_coverage
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.local_average
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_finite_message_bound
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_no_loss_of_root_load
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.parentPotential_local
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_no_loss_of_parent_charge
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_list_bound
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_list_loss_factor
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSTwoLevel.certifiedFS
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSTwoLevel.certifiedSoundness
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.affine_sound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSTwoLevel.affine_soundness
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.root_load_ge_wire_orbit
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.root_load_ge_mask_orbit
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.assigned_payload_unique
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.high_target_covered_or_proper
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.twoLevel_fullResponse_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.large_response
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.response_fraction_le_envelope
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.localEnvelope_mean
#guard_msgs (drop info) in #check RecursivePolygero.Child.verify_iff
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.wireVerify_eq
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.extract
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.extractTranscript_valid
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.run_valid
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.randomTargetProbability_le
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.extraction_failure
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.error_eq_product
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.error_le_sum
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.extractWitness_valid
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.wireExtract_valid
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.wire_extraction_failure
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.soundness_of_extraction
#guard_msgs (drop info) in #check RecursivePolygero.DirectBinomial.normalized_excess_le_of_hahn
#guard_msgs (drop info) in #check RecursivePolygero.DirectBinomial.normalized_excess_le_of_hahnCertificate
#guard_msgs (drop info) in #check RecursivePolygero.HahnSystemCertificate.ofHahnCertificate
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.systemCap_excess_of_hahn
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.localEnvelope_mean_of_hahn
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.HahnProfileProof.wireExtract_valid
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.HahnProfileProof.wire_extraction_failure
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.HahnProfileProof.soundness_of_extraction
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_wireExtract
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_error
#guard_msgs (drop info) in #check RecursivePolygero.Protocol.HahnProfileProof.wireExtract_independent

#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.role_oracle_sound
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_list_oracle_sound
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.weightedExceptions_mean_le

#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.fixed_rigidExceptionExcess_mean_le_two
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.child_block_oracle_sound_fixed
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.whole_block_oracle_sound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSNonuniformSpectrum.query_oracle_sound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSWholeBlock81.certifiedAffineFS
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSWholeBlock81.certifiedSoundness
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.StoppedSpectrum.conditionalCapacity_repeatPrice_mean_le_defect_split
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSDefectSpectrum.query_oracle_sound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSDefect81.certifiedSoundness
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSDefect81.certifiedSoundness_iop
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSCompletion81.certifiedSoundness_iop
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSBaselineAware81.certifiedSoundness_strongIOP
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSIOPReference81.interactive_failure_le_strongIOP

#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.assigned_union_capacity_le
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.assigned_query_union_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.assignedExceptionQuery_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.childExceptionQuery_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.queryExceptionEvent_local
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.activated_exception_consumption_iff
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.two_child_attempts_reuse

#guard_msgs (drop info) in #check Bcs.StoppedPotential.stoppedValue_le
#guard_msgs (drop info) in #check Bcs.StoppedPotential.average_repeatPrice_le
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.queryTargetExcess_mean_le
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.geometry_exists_failure_tree
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_violation
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSGrindingObstruction.concrete_no_loss_soundness_violation
#guard_msgs (drop info) in #check CodingTheory.IntegerOccupancy.uniformFamilyBound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedAffineFS
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSIntegerAffine.certifiedSoundness
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSRetunedAffine.fixedCertifiedSoundness
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.StoppedSpectrum.spectrum_layers_le
#guard_msgs (drop info) in #check RecursivePolygero.ProfileAnalysis.high_assigned_payload_unique_of_capacity
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.failure_capacity_cover
#guard_msgs (drop info) in #check RecursivePolygero.FiatShamir.TwoLevel.query_stopped_oracle_sound_of_spectrum

open Lean Elab Command

private partial def proofDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
      if seen.contains name then proofDependencies env rest seen
      else
        let deps := match env.find? name with
          | some info => info.getUsedConstantsAsSet.toList
          | none => []
        proofDependencies env (deps ++ rest) (seen.insert name)

-- Check every owned declaration, including private proofs and legacy namespaces.
run_cmd do
  let env ← getEnv
  for required in #[
      ``RecursivePolygero.explosion,
      ``RecursivePolygero.ProximityGap.polynomial_error_threshold,
      ``RecursivePolygero.Local.PolynomialClosure.canonical_core,
      ``RecursivePolygero.Local.PolynomialClosure.core_union_mds,
      ``RecursivePolygero.Local.ReducedSystems.associated_intersection,
      ``RecursivePolygero.DirectBinomial.normalized_excess_le,
      ``RecursivePolygero.ProfileAnalysis.large_response,
      ``RecursivePolygero.ProfileAnalysis.localEnvelope_mean,
      ``RecursivePolygero.Child.verify_iff,
      ``RecursivePolygero.Protocol.ProfileProof.randomTargetProbability_le,
      ``RecursivePolygero.Protocol.ProfileProof.extractWitness_valid,
      ``RecursivePolygero.Protocol.ProfileProof.extractWitness_failure,
      ``RecursivePolygero.Protocol.ProfileProof.wireExtract_valid,
      ``RecursivePolygero.Protocol.ProfileProof.wire_extraction_failure,
      ``RecursivePolygero.Protocol.ProfileProof.soundness_of_extraction,
      ``RecursivePolygero.DirectBinomial.normalized_excess_le_of_hahn,
      ``RecursivePolygero.DirectBinomial.normalized_excess_le_of_activeFamilyBound,
      ``RecursivePolygero.HahnSystemCertificate.ofHahnCertificate,
      ``RecursivePolygero.ProfileAnalysis.localEnvelope_mean_of_hahn,
      ``RecursivePolygero.Protocol.HahnProfileProof.wireExtract_valid,
      ``RecursivePolygero.Protocol.HahnProfileProof.wire_extraction_failure,
      ``RecursivePolygero.Protocol.HahnProfileProof.soundness_of_extraction] do
    unless RecursivePolygero.StableAPI.isPrecious env required do
      throwError "Public Polygero declaration lost precious API protection: {required}"
  for required in #[
      ``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_wireExtract,
      ``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_error,
      ``RecursivePolygero.Protocol.HahnProfileProof.wireExtract_independent] do
    unless RecursivePolygero.StableAPI.isPrecious env required do
      throwError "Analysis invariance declaration lost precious API protection: {required}"
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    unless owner == `polygero || owner.toString.startsWith "polygero." do continue
    if info.isAxiom then throwError "Unexpected imported axiom: {name}"
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
  let extracted := proofDependencies env
    [``RecursivePolygero.Protocol.ProfileProof.wire_extraction_failure]
  for required in #[
      ``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_extract,
      ``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_error,
      ``RecursivePolygero.Protocol.HahnProfileProof.randomTargetProbability_le,
      ``RecursivePolygero.Protocol.ProfileProof.inducedFamily_frequency,
      ``RecursivePolygero.ProfileAnalysis.localEnvelope_mean_of_hahn,
      ``RecursivePolygero.ProfileAnalysis.response_fraction_le_envelope,
      ``RecursivePolygero.ProfileAnalysis.large_response,
      ``RecursivePolygero.ProfileAnalysis.certify,
      ``RecursivePolygero.ProfileAnalysis.systemLabel,
      ``RecursivePolygero.affine_rows_of_full_consistency,
      ``RecursivePolygero.polynomialArithmeticMatches_card,
      ``RecursivePolygero.Local.ReducedSystems.badChallenges_card,
      ``RecursivePolygero.Local.ReducedSystems.associated_intersection,
      ``RecursivePolygero.Local.Shift.rank_on_core_subset,
      ``RecursivePolygero.DirectBinomial.normalized_excess_le,
      ``RecursivePolygero.SystemException.random_target_envelope_mean,
      ``RecursivePolygero.PuncturedDecoder.complete,
      ``RecursivePolygero.Child.verify_iff,
      ``RecursivePolygero.coefficientStatement_satisfies,
      ``RecursivePolygero.Local.Polygero.verify_openOracle_iff,
      ``RecursivePolygero.Protocol.expandWireStrategy,
      ``RecursivePolygero.Instance.expandWireOracle,
      ``RecursivePolygero.scanRecoverAt,
      ``RecursivePolygero.executionVerify] do
    unless extracted.contains required do
      throwError "Extraction omits its concrete proof dependency: {required}"
  let soundness := proofDependencies env
    [``RecursivePolygero.Protocol.ProfileProof.soundness_of_extraction]
  for required in #[
      ``RecursivePolygero.Protocol.ProfileProof.wireExtract_valid,
      ``RecursivePolygero.Protocol.ProfileProof.wire_extraction_failure] do
    unless soundness.contains required do
      throwError "Soundness is not derived from extraction: {required}"
  let hahnExtracted := proofDependencies env
    [``RecursivePolygero.Protocol.HahnProfileProof.wire_extraction_failure,
     ``RecursivePolygero.HahnSystemCertificate.ofHahnCertificate]
  for required in #[
      ``RecursivePolygero.DirectBinomial.normalized_excess_le_of_activeFamilyBound,
      ``RecursivePolygero.ProfileAnalysis.localEnvelope_mean_of_hahn,
      ``CodingTheory.HahnDelsarte.uniformFamilyBound_of_certificate] do
    unless hahnExtracted.contains required do
      throwError "Hahn extraction omits its concrete proof dependency: {required}"
  let hahnSoundness := proofDependencies env
    [``RecursivePolygero.Protocol.HahnProfileProof.soundness_of_extraction]
  for required in #[
      ``RecursivePolygero.Protocol.HahnProfileProof.wireExtract_valid,
      ``RecursivePolygero.Protocol.HahnProfileProof.wire_extraction_failure] do
    unless hahnSoundness.contains required do
      throwError "Hahn soundness is not derived from extraction: {required}"
  let conversion := proofDependencies env
    [``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_wireExtract]
  unless conversion.contains
      ``RecursivePolygero.Protocol.ProfileProof.toHahnProfileProof_runTranscript do
    throwError "Hahn conversion does not preserve the transcript extractor"
  let invariant := proofDependencies env
    [``RecursivePolygero.Protocol.HahnProfileProof.wireExtract_independent]
  unless invariant.contains
      ``RecursivePolygero.Protocol.HahnProfileProof.runTranscript_independent do
    throwError "Hahn certificate independence does not reach the transcript extractor"
  let responseTransfer := proofDependencies env
    [``RecursivePolygero.FiatShamir.twoLevel_fullResponse_mean_le]
  for required in #[
      ``RecursivePolygero.ProfileAnalysis.assigned_payload_unique,
      ``RecursivePolygero.ProfileAnalysis.assigned_arithmetic_canonical,
      ``RecursivePolygero.ProfileAnalysis.full_response_excess_le,
      ``RecursivePolygero.ProfileAnalysis.localIncidence_mean_of_hahn] do
    unless responseTransfer.contains required do
      throwError "Response transfer omits its concrete rigidity/incidence dependency: {required}"
  let responseCoverage := proofDependencies env
    [``RecursivePolygero.ProfileAnalysis.high_target_covered_or_proper]
  unless responseCoverage.contains ``RecursivePolygero.ProfileAnalysis.large_response_assigned do
    throwError "Response coverage omits the concrete Polygero assignment"
  let parentCharge := proofDependencies env
    [``RecursivePolygero.FiatShamir.TwoLevel.fs_no_loss_of_parent_charge]
  for required in #[
      ``RecursivePolygero.FiatShamir.TwoLevel.parentPotential_local,
      ``RecursivePolygero.ProfileAnalysis.localEnvelope_mean_of_hahn,
      ``Bcs.TotalOracle.Footprint.event_le_expected_budget,
      ``Bcs.TotalOracle.Footprint.event_le_of_parent_charge,
      ``Bcs.TotalOracle.Footprint.hits_off] do
    unless parentCharge.contains required do
      throwError "Parent charge omits its concrete envelope/freshness dependency: {required}"
  let listCompiler := proofDependencies env
    [``RecursivePolygero.FiatShamir.TwoLevel.fs_list_loss_factor]
  for required in #[
      ``RecursivePolygero.FiatShamir.TwoLevel.failure_list_cover,
      ``RecursivePolygero.ProfileAnalysis.highSystems_card_le,
      ``RecursivePolygero.DirectBinomial.active_card_le_of_uniformFamilyBound,
      ``RecursivePolygero.Local.ReducedSystems.associated_intersection,
      ``RecursivePolygero.ProfileAnalysis.large_response_assigned,
      ``RecursivePolygero.ProfileAnalysis.systemExceptions_mean,
      ``RecursivePolygero.ProfileAnalysis.rank_bad_mean,
      ``RecursivePolygero.FiatShamir.induced_target_frequency_le,
      ``Bcs.TotalOracle.Footprint.selected_singleton_event_le] do
    unless listCompiler.contains required do
      throwError "List compiler omits its concrete coverage/counting dependency: {required}"

  let affineCompiler := proofDependencies env
    [``RecursivePolygero.FiatShamir.TwoLevel.fs_list_affine_bound]
  for required in #[
      ``Bcs.AffineBlock.oracle_parallel_max,
      ``RecursivePolygero.FiatShamir.TwoLevel.role_oracle_sound,
      ``RecursivePolygero.FiatShamir.TwoLevel.failure_list_cover,
      ``RecursivePolygero.FiatShamir.TwoLevel.queryRisk_mean_le,
      ``RecursivePolygero.ProfileAnalysis.listBad_mean_le] do
    unless affineCompiler.contains required do
      throwError "Affine compiler omits concrete local bound/cover: {required}"

run_cmd do
  let deps := proofDependencies (← getEnv)
    [``RecursivePolygero.FiatShamir.TwoLevel.childExceptionQuery_mean_le]
  for name in #[
      ``RecursivePolygero.Child.verify_iff,
      ``RecursivePolygero.ProfileAnalysis.large_response_assigned,
      ``RecursivePolygero.ProfileAnalysis.assign_associated,
      ``RecursivePolygero.ProfileAnalysis.assigned_primary_unique,
      ``RecursivePolygero.ProfileAnalysis.assigned_union_capacity_le,
      ``RecursivePolygero.Local.PolynomialClosure.canonical_closures_eq,
      ``RecursivePolygero.ProfileAnalysis.weightedExceptions_mean_le,
      ``RecursivePolygero.ProfileAnalysis.highSystems_capacity_sum_le] do
    unless deps.contains name do
      throwError "Adaptive capacity coverage omits actual dependency {name}"

#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSCompiled81.certified_bound
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSCompiled81.certified_comparisons
#guard_msgs (drop info) in #check RecursivePolygero.Benchmarks.FSCompiled81.false_statement_bound
