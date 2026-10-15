import polygero
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! Public recursive extraction and soundness endpoints. -/
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
