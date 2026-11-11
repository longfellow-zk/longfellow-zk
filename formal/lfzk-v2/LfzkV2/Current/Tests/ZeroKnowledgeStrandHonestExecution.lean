import LfzkV2.Current.ZeroKnowledge.StrandHonestExecution
import Lean.Util.CollectAxioms

/-! Successful outputs are inverted from actual execution, preserving the
original commitment and nonce tape rather than assuming a decoded proof. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestExecution
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for endpoint in #[``StrandHonestExecution.rawReal_result, ``StrandHonestExecution.rawReal_some] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    let used := info.type.getUsedConstants
    unless used.contains ``StrandCanonicalHiding.rawReal &&
        used.contains ``StrandCanonicalHiding.response &&
        used.contains ``StrandCanonicalBackend.finish && used.contains ``Merkle.Indexed.openCore do
      throwError "Endpoint {endpoint} lost its actual execution or original opening"
    if used.contains ``CompleteCanonicalVerifier.statementAt then
      throwError "Execution inversion {endpoint} requires a supplied parse certificate"
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestExecution
