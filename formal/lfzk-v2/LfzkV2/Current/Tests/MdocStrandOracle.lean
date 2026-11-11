import LfzkV2.Current.MdocStrandOracle
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.MdocStrandOracle

/--
info: 'LfzkV2.Current.MdocStrandOracle.averaged_linear_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.averaged_linear_ratio_le

/--
info: 'LfzkV2.Current.MdocStrandOracle.ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.ratio_le

/--
info: 'LfzkV2.Current.MdocStrandOracle.averaged_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.averaged_ratio_le

/--
info: 'LfzkV2.Current.MdocStrandOracle.event_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.event_verified

/--
info: 'LfzkV2.Current.MdocStrandOracle.original_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.original_trace

/--
info: 'LfzkV2.Current.MdocStrandOracle.verifier_actual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandOracle.verifier_actual

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.MdocStrandOracle.ratio_le, ``LfzkV2.Current.MdocStrandOracle.averaged_ratio_le] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``Survival.Rate7.failureBound do
      throwError "Primary endpoint {endpoint} does not use the exact c/q bound"
  for endpoint in #[``LfzkV2.Current.MdocStrandOracle.averaged_nonvacuous,
      ``LfzkV2.Current.MdocStrandOracle.averaged_polynomial_ratio_le,
      ``LfzkV2.Current.MdocStrandOracle.averaged_mdoc_approximation] do
    for ax in ← Lean.collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.MdocStrandOracle
