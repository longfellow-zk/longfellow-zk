import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Mdoc.RuntimeSoundness
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.MdocStrandSoundness

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.Mdoc.RuntimeSoundness.fixed_setup_ratio_le, ``LfzkV2.Current.Mdoc.RuntimeSoundness.ratio_le] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``LfzkV2.Current.Soundness.Rate7.failureBound do
      throwError "Primary endpoint {endpoint} does not use the exact c/q bound"
  for ax in ← Lean.collectAxioms ``LfzkV2.Current.Mdoc.RuntimeSoundness.nonvacuous do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in the nonvacuous margin"

end LfzkV2.Current.Tests.MdocStrandSoundness

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Mdoc.RuntimeSoundness.linear_ratio_le,
  ``LfzkV2.Current.Mdoc.RuntimeSoundness.ratio_le,
  ``LfzkV2.Current.Mdoc.RuntimeSoundness.observation_original,
  ``LfzkV2.Current.Mdoc.RuntimeSoundness.observation_verifier]
