import LfzkV2.Current.StrandProtocol
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests.StrandProtocol

/--
info: 'LfzkV2.Current.StrandProtocol.soundness_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.StrandProtocol.soundness_linear

/--
info: 'LfzkV2.Current.StrandProtocol.accepted_decoded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.StrandProtocol.accepted_decoded

/--
info: 'LfzkV2.Current.StrandProtocol.authenticated' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.StrandProtocol.authenticated

/--
info: 'LfzkV2.Current.StrandProtocol.recovered_failure_charge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.StrandProtocol.recovered_failure_charge

/--
info: 'LfzkV2.Current.StrandProtocol.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LfzkV2.Current.StrandProtocol.soundness

/- The primary names expose the chronological envelope, rather than a
retained linear theorem or a parallel experimental endpoint. -/
run_cmd do
  let env ← Lean.getEnv
  for endpoint in #[``LfzkV2.Current.StrandProtocol.soundness] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    unless info.type.getUsedConstants.contains ``Survival.Hybrid.envelope do
      throwError "Primary endpoint {endpoint} does not use the survival envelope"

end LfzkV2.Current.Tests.StrandProtocol
