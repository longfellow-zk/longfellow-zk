import LfzkV2.Current.Mdoc.Completeness
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestFrontend
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestExecution
import Lean.Util.CollectAxioms

/-! The honest-runtime endpoint accepts an actually returned proof from
ordinary witness premises, deriving all parser and authentication facts. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestRuntime
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let endpoint := ``Mdoc.Completeness.rawReal_some_accepts
  let env ← getEnv
  let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
  let used := info.type.getUsedConstants
  unless used.contains ``StrandCanonicalHiding.rawReal &&
      used.contains ``StrandVerifier.verify &&
      used.contains ``MdocWitness.HashValid && used.contains ``MdocWitness.ReadDisjoint do
    throwError "Honest runtime lost actual execution, actual verification or ordinary-witness premises"
  if used.contains ``CompleteCanonicalVerifier.statementAt ||
      used.contains ``MdocWitness.UniformHashValid then
    throwError "Honest runtime exposes a derived parse or uniform witness certificate"
  unless used.contains ``Mdoc.Runtime && used.contains ``Protocol.ExecutionSampler do
    throwError "Honest runtime must share the public setup and executable sampler"
  if used.contains ``Protocol.SamplerLaws then
    throwError "Conditional honest acceptance must not require sampler balance"
  for ax in ← collectAxioms endpoint do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestRuntime
