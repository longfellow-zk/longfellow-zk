import LfzkV2.Current.ZeroKnowledge.StrandHonestFrontend
import Lean.Util.CollectAxioms

/-! Guard the actual frontend constructor and ordinary-witness interface. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestFrontend
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let endpoint := ``StrandHonestFrontend.exists_satisfied
  let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
  let used := info.type.getUsedConstants
  unless used.contains ``FrontendCanonicalRows.honestBody &&
      used.contains ``StrandCanonicalFullCoupling.actualOracle &&
      used.contains ``MdocWitness.HashValid && used.contains ``MdocWitness.HashNoninterference do
    throwError "Honest frontend lost its actual constructor or ordinary-witness premises"
  if used.contains ``MdocWitness.UniformHashValid then
    throwError "Honest frontend exposes the derived uniform witness premise"
  for endpoint in #[``StrandHonestFrontend.exists_satisfied,
      ``StrandHonestFrontend.frontend_commitment] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestFrontend
