import LfzkV2.Current.Mdoc.Soundness
import LfzkV2.Current.Mdoc.VerifierPrivacy
import LfzkV2.Current.Mdoc.Completeness
import LfzkV2.Current.Tests.ProofAudit

/-! Declaration-level regression guard. Sharing a file with live definitions
must not preserve a superseded verifier, simulator or composition interface. -/
namespace LfzkV2.Current.Tests.RuntimeBoundary
open Lean Elab Command

run_cmd do
  let forbidden := #[
    "LfzkV2.Current.CommitmentOracle", "LfzkV2.Current.MerkleReplay",
    "LfzkV2.Current.GlobalCharges",
    "LfzkV2.Current.ApplicationCharging.FrontendLocal",
    "LfzkV2.Current.ApplicationCharging.Configuration",
    "LfzkV2.Current.ApplicationCharging.PrefixConfiguration",
    "LfzkV2.Current.Soundness.Recovery.hashCharge_sum_le",
    "LfzkV2.Current.Soundness.Recovery.auxiliaryCount",
    "LfzkV2.Current.Soundness.Recovery.recovery_failure_ratio_le",
    "LfzkV2.Current.Soundness.Recovery.meanAuxiliary",
    "LfzkV2.Current.Soundness.Recovery.recoveredEvent",
    "LfzkV2.Current.Soundness.Recovery.recoveredProbability",
    "LfzkV2.Current.Soundness.Recovery.failure_ratio_le",
    "LfzkV2.Current.OrderedOpening.read", "LfzkV2.Current.OrderedOpening.read_replay",
    "LfzkV2.Current.OrderedOpening.read_indices_replay",
    "LfzkV2.Current.Mdoc.SetupFamily.Point", "LfzkV2.Current.Mdoc.SetupFamily.Canonical",
    "LfzkV2.Current.Mdoc.SetupFamily.pointFintype", "LfzkV2.Current.Mdoc.SetupFamily.codec",
    "LfzkV2.Current.RuntimeVerifier.framing", "LfzkV2.Current.RuntimeVerifier.encoding",
    "LfzkV2.Current.RuntimeVerifier.statementAt", "LfzkV2.Current.RuntimeVerifier.decode",
    "LfzkV2.Current.RuntimeVerifier.Checks", "LfzkV2.Current.RuntimeVerifier.verify",
    "LfzkV2.Current.RuntimeVerifier.verify_true_iff",
    "LfzkV2.Current.RuntimeAdaptiveVerifier.ChecksWithSeal",
    "LfzkV2.Current.RuntimeAdaptiveVerifier.Checks", "LfzkV2.Current.RuntimeAdaptiveVerifier.verify",
    "LfzkV2.Current.RuntimeAdaptiveVerifier.verify_true_iff",
    "LfzkV2.Current.RuntimeAdaptiveMerkle.setup", "LfzkV2.Current.RuntimeAdaptiveMerkle.cutOracle",
    "LfzkV2.Current.RuntimeCover.QuerySetup", "LfzkV2.Current.RuntimeCover.PublicQueries",
    "LfzkV2.Current.RuntimeCover.authentication", "LfzkV2.Current.RuntimeCover.decoded_failure_cover",
    "LfzkV2.Current.RuntimeCover.verified_failure_cover",
    "LfzkV2.Current.RuntimeCover",
    "LfzkV2.Current.RuntimeBackend", "LfzkV2.Current.RuntimeSelection",
    "LfzkV2.Current.RuntimeRoles", "LfzkV2.Current.RuntimeParameters",
    "LfzkV2.Current.CanonicalVerifierAgreement", "LfzkV2.Current.ProtocolProbability",
    "LfzkV2.Current.ZeroKnowledge.OracleProgramming", "LfzkV2.Current.ZeroKnowledge.OracleRuntime",
    "LfzkV2.Current.ZeroKnowledge.OracleResponse",
    "LfzkV2.Current.ZeroKnowledge.Frontend.History.opening_properties",
    "LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalSimulation.opening_query",
    "LfzkV2.Current.ZeroKnowledge.CompleteBody", "LfzkV2.Current.ZeroKnowledge.CompleteBackend",
    "LfzkV2.Current.ZeroKnowledge.CompleteOpening", "LfzkV2.Current.ZeroKnowledge.CompleteVerifier",
    "LfzkV2.Current.ZeroKnowledge.HonestTranscript",
    "TranscriptV2.Composition.SoundnessRealization", "TranscriptV2.SharedReduction"]
  for (name,_) in (← getEnv).constants do
    let text := name.toString
    if forbidden.any (fun stem => text == stem || text.startsWith (stem ++ ".")) then
      throwError "Superseded runtime declaration remains: {name}"

/- The public statements must retain their actual events and experiments.
The separate proof-path guards check their connection to component proofs. -/
run_cmd do
  let env ← getEnv
  for (endpoint, required) in #[
      (``Mdoc.Soundness.averaged_ratio_le,
        #[``Mdoc.Soundness.event, ``Soundness.Rate7.failureBound]),
      (``Mdoc.ZeroKnowledge.statClose,
        #[``StatClose, ``Mdoc.ZeroKnowledge.honest, ``Mdoc.ZeroKnowledge.simulate])] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    let used := info.type.getUsedConstants
    for dependency in required do
      unless used.contains dependency do
        throwError "Endpoint {endpoint} lost its end-to-end conclusion {dependency}"
  for (declaration, required) in #[
      (``Mdoc.Soundness.event,
        #[``ProofOutput.read, ``Mdoc.RuntimeSoundness.verify,
          ``Mdoc.Soundness.extract, ``Mdoc.Soundness.Valid]),
      (``Mdoc.Soundness.Valid, #[``MdocWitness.Valid])] do
    let some info := env.find? declaration | throwError "Missing event {declaration}"
    let some body := info.value? true | throwError "Missing definition {declaration}"
    let used := body.getUsedConstants
    for dependency in required do
      unless used.contains dependency do
        throwError "Event {declaration} lost its runtime meaning {dependency}"

run_cmd ProofAudit.standardAxioms #[``Mdoc.Soundness.averaged_ratio_le,
  ``Mdoc.Soundness.averaged_linear_ratio_le, ``Mdoc.Soundness.averaged_nonvacuous,
  ``Mdoc.Soundness.averaged_mdoc_approximation, ``Mdoc.ZeroKnowledge.statClose,
  ``Mdoc.ZeroKnowledge.statClose_at_query_budget, ``Mdoc.VerifierPrivacy.acceptance_probability,
  ``Mdoc.Completeness.rawReal_some_accepts]

end LfzkV2.Current.Tests.RuntimeBoundary
