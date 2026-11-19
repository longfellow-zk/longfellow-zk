import LfzkV2.Current.Mdoc.Soundness
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
  for endpoint in #[``Current.Mdoc.Soundness.averaged_ratio_le,
      ``Current.Mdoc.Soundness.averaged_nonvacuous,
      ``Current.Mdoc.Soundness.averaged_mdoc_approximation] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
  let mut pending := [``Current.Mdoc.Soundness.averaged_ratio_le]
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
      ``HashCircuit.checks_iff_of_readDisjoint,
      ``ApplicationViews.rescaleBad_card_mul_le,
      ``ApplicationViews.conversionBad_card_mul_le,
      ``BackendFS.high_sum_active,
      ``Survival.CausalCharges.failure_le_support,
      ``Soundness.LocalCharges.prefixCharge_eq_runtime, ``Soundness.LocalCharges.prefixOracle_eq_original] do
    unless visited.contains required do
      throwError "Application endpoint disconnected from {required}"
  for moduleName in env.header.moduleNames do
    if #["Survival.PrefixCache", "Survival.ChargeMonitor", "Survival.Saturation",
        "LfzkV2.Current.ChainedFS", "LfzkV2.Current.ChainedSupport",
        "LfzkV2.Current.RuntimeAdaptiveReduction", "LfzkV2.Current.SurvivalPrefix"].contains moduleName.toString then
      throwError "Application endpoint imports a retired interface {moduleName}"

end LfzkV2.Current.Tests.MdocSoundness
