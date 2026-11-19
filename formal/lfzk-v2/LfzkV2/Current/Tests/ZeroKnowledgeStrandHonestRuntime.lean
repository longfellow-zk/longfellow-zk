import LfzkV2.Current.Mdoc.Completeness
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestFrontend
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestExecution
import Lean.Util.CollectAxioms

/-! The honest-runtime endpoints accept the honest prover's proof from
ordinary witness premises, deriving all parser and authentication facts,
and `accepts` has no abort branch once every boundary samples. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestRuntime
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- The prover is the actual experiment's, and the verifier the runtime's.
  for (definition, required) in #[(``Mdoc.Completeness.prove, ``StrandCanonicalExecution.rawReal),
      (``Mdoc.Completeness.verify, ``StrandVerifier.verify),
      (``Mdoc.Completeness.Sampled, ``TranscriptV2.StrandVerifier.sampled)] do
    let some info := env.find? definition | throwError "Missing definition {definition}"
    let some body := info.value? true | throwError "Missing body of {definition}"
    unless body.getUsedConstants.contains required do
      throwError "{definition} lost {required}"
  for endpoint in #[``Mdoc.Completeness.some_accepts, ``Mdoc.Completeness.accepts] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    let used := info.type.getUsedConstants
    unless used.contains ``Mdoc.Completeness.prove &&
        used.contains ``Mdoc.Completeness.verify &&
        used.contains ``MdocWitness.HashValid do
      throwError "Honest runtime lost actual execution, actual verification or ordinary-witness premises"
    if used.contains ``CompleteCanonicalVerifier.statementAt ||
        used.contains ``MdocWitness.UniformHashValid || used.contains ``HashCircuit.ReadDisjoint then
      throwError "Honest runtime exposes a derived parse or uniform witness certificate"
    unless used.contains ``Mdoc.Runtime && used.contains ``Protocol.ExecutionSampler do
      throwError "Honest runtime must share the public setup and executable sampler"
    if used.contains `LfzkV2.Current.Protocol.SamplerLaws then
      throwError "Honest acceptance must not require sampler balance"
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
  -- The non-abort premise is the sampling of every boundary, nothing stronger.
  let some info := env.find? ``Mdoc.Completeness.accepts | throwError "Missing accepts"
  unless info.type.getUsedConstants.contains ``Mdoc.Completeness.Sampled do
    throwError "Completeness lost its non-abort premise"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestRuntime
