import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Mdoc.OracleSoundness
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.MdocStrandOracle

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.Mdoc.OracleSoundness.ratio_le, ``LfzkV2.Current.Mdoc.OracleSoundness.averaged_ratio_le] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``LfzkV2.Current.Soundness.Rate7.failureBound do
      throwError "Primary endpoint {endpoint} does not use the exact c/q bound"
  for endpoint in #[``LfzkV2.Current.Mdoc.OracleSoundness.averaged_nonvacuous,
      ``LfzkV2.Current.Mdoc.OracleSoundness.averaged_polynomial_ratio_le,
      ``LfzkV2.Current.Mdoc.OracleSoundness.averaged_mdoc_approximation] do
    for ax in ← Lean.collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.MdocStrandOracle

run_cmd LfzkV2.Current.Tests.ProofAudit.standardAxioms #[
  ``LfzkV2.Current.Mdoc.OracleSoundness.averaged_linear_ratio_le,
  ``LfzkV2.Current.Mdoc.OracleSoundness.ratio_le,
  ``LfzkV2.Current.Mdoc.OracleSoundness.averaged_ratio_le,
  ``LfzkV2.Current.Mdoc.OracleSoundness.event_verified,
  ``LfzkV2.Current.Mdoc.OracleSoundness.original_trace,
  ``LfzkV2.Current.Mdoc.OracleSoundness.verifier_actual]
