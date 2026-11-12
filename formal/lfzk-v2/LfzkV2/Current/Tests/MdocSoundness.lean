import LfzkV2.Current.MdocSoundness
import Lean.Util.CollectAxioms

/-! Guard the application conclusion and the proof path, including the
formerly disconnected actual-request bridge. The standalone import also
checks that soundness does not depend on simulator modules. -/
namespace LfzkV2.Current.Tests.MdocSoundness
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for moduleName in env.header.moduleNames do
    if moduleName.toString.startsWith "LfzkV2.Current.ZeroKnowledge" ||
        moduleName.toString.startsWith "LfzkV1" then
      throwError "Application soundness imports forbidden module {moduleName}"
  for endpoint in #[``Current.MdocSoundness.averaged_ratio_le,
      ``Current.MdocSoundness.averaged_nonvacuous,
      ``Current.MdocSoundness.averaged_mdoc_approximation] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
  let mut pending := [``Current.MdocSoundness.averaged_ratio_le]
  let mut visited : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    if let some info := env.find? name then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := info.value? true then
        pending := value.getUsedConstants.toList ++ pending
  for required in #[``CanonicalRuntime.decoded_true_at_request,
      ``MdocWitness.HashValid,``MdocWitness.extractedPrivate,
      ``HashCircuit.checks_iff_of_readDisjoint] do
    unless visited.contains required do
      throwError "Application endpoint disconnected from {required}"

end LfzkV2.Current.Tests.MdocSoundness
