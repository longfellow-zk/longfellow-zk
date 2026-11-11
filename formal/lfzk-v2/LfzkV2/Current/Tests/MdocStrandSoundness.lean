import LfzkV2.Current.MdocStrandSoundness
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.MdocStrandSoundness

/--
info: 'LfzkV2.Current.MdocStrandSoundness.linear_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandSoundness.linear_ratio_le

/--
info: 'LfzkV2.Current.MdocStrandSoundness.ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandSoundness.ratio_le

/--
info: 'LfzkV2.Current.MdocStrandSoundness.observation_original' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandSoundness.observation_original

/--
info: 'LfzkV2.Current.MdocStrandSoundness.observation_verifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.MdocStrandSoundness.observation_verifier

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.MdocStrandSoundness.fixed_setup_ratio_le, ``LfzkV2.Current.MdocStrandSoundness.ratio_le] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``Survival.Rate7.failureBound do
      throwError "Primary endpoint {endpoint} does not use the exact c/q bound"
  for ax in ← Lean.collectAxioms ``LfzkV2.Current.MdocStrandSoundness.nonvacuous do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected axiom {ax} in the nonvacuous margin"

end LfzkV2.Current.Tests.MdocStrandSoundness
