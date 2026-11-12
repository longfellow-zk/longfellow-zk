import LfzkV2.Current.Parameters.Rate7
import Lean.Util.CollectAxioms

/-! The production joint mdoc certificate has its own shared two-field
budget. It is distinct from the universal nonrecursive tuning profiles. -/
namespace MdocJointProfile

abbrev profile := LfzkV2.Current.FixedRate.Rate7.certificate

theorem geometry : (profile.k, profile.s, profile.n, profile.t) = (349, 12, 2443, 84) := rfl

open Lean Elab Command in
run_cmd do
  for endpoint in #[``profile,
      ``LfzkV2.Current.FixedRate.Rate7.Active.family_bound,
      ``LfzkV2.Current.FixedRate.Rate7.Binary.family_bound,
      ``LfzkV2.Current.FixedRate.Rate7.Prime.family_bound] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in production mdoc certificate {endpoint}"

end MdocJointProfile
