import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Soundness.Composition
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.StrandProtocol

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.Soundness.Composition.soundness] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``Survival.Hybrid.envelope do
      throwError "Primary endpoint {endpoint} does not use the survival envelope"

private def explicitInputs : Lean.Expr → List Lean.Name
  | .forallE name _ body info =>
      (if info == .default then [name] else []) ++ explicitInputs body
  | _ => []

run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.Soundness.Composition.soundness,
      ``LfzkV2.Current.Soundness.Composition.soundness_linear] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless (explicitInputs info.type).take 3 == [`S,`M,`A] do
      throwError "Composition {endpoint} must take setup, sampler and adversary records"

end LfzkV2.Current.Tests.StrandProtocol

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Soundness.Composition.soundness_linear,
  ``LfzkV2.Current.Soundness.Runtime.accepted_decoded,
  ``LfzkV2.Current.Soundness.Runtime.authenticated,
  ``LfzkV2.Current.Soundness.Runtime.recovered_failure_charge,
  ``LfzkV2.Current.Soundness.Composition.soundness]
