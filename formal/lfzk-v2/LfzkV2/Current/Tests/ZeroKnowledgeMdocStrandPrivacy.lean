import LfzkV2.Current.Mdoc.VerifierPrivacy
import Lean.Util.CollectAxioms

/-! The numbered-strand endpoint derives setup and raw support internally,
and its acceptance observer is the actual indexed runtime verifier. Guard
all new bridges as well as the complete privacy and concrete-budget results. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocStrandPrivacy
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for endpoint in #[``Mdoc.ZeroKnowledge.statClose,
      ``Mdoc.VerifierPrivacy.acceptance_probability] do
    let some info := env.find? endpoint | throwError "Missing endpoint {endpoint}"
    liftTermElabM do
      Meta.forallTelescope info.type fun binders _ => do
        let mut contextBinder : Option Expr := none
        for binder in binders do
          if (← binder.fvarId!.getDecl).userName == `Context then
            contextBinder := some binder
        let some context := contextBinder | throwError "Endpoint {endpoint} lost its private context"
        for policy in #[`original, `remaining] do
          let mut found := false
          for binder in binders do
            if (← binder.fvarId!.getDecl).userName == policy then
              let .forallE _ domain _ _ ← Meta.inferType binder |
                throwError "Endpoint {endpoint} has a nonfunctional {policy} policy"
              unless ← Meta.isDefEq domain context do
                throwError "Endpoint {endpoint} no longer permits a Context-indexed {policy} policy"
              found := true
          unless found do
            throwError "Endpoint {endpoint} lost its {policy} policy"
    let used := info.type.getUsedConstants
    unless used.contains ``Mdoc.ZeroKnowledge.Reachable &&
        used.contains ``MdocWitness.ReadDisjoint && used.contains ``MdocWitness.HashValid do
      throwError "Endpoint {endpoint} lost reached-witness or static-circuit premises"
    if used.contains ``MdocWitness.UniformHashValid then
      throwError "Endpoint {endpoint} exposes the derived uniform witness premise"
    unless used.contains ``Protocol.ExecutionSampler do
      throwError "Endpoint {endpoint} does not use the shared executable sampler"
    if used.contains `LfzkV2.Current.Protocol.SamplerLaws then
      throwError "Privacy must not assume the soundness sampling balance law"
  for endpoint in #[``Mdoc.ZeroKnowledge.simulate,
      ``Mdoc.ZeroKnowledge.honest] do
    let some info := env.find? endpoint | throwError "Missing experiment {endpoint}"
    unless info.type.getUsedConstants.contains ``Protocol.Execution.PublicView do
      throwError "Experiment {endpoint} does not expose the shared public view"
  let some simulator := env.find? ``Mdoc.ZeroKnowledge.simulate |
    throwError "Missing witness-free simulator"
  liftTermElabM do
    Meta.forallTelescope simulator.type fun binders _ => do
      for binder in binders do
        let name := (← binder.fvarId!.getDecl).userName
        if #[`original,`remaining,`valid,`signature].contains name then
          throwError "Simulator has a witness-dependent input {name}"
  let mut pending := [``Mdoc.ZeroKnowledge.statClose]
  let mut visited : NameSet := {}
  while let name :: rest := pending do
    pending := rest
    if visited.contains name then continue
    visited := visited.insert name
    if let some info := env.find? name then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := info.value? true then
        pending := value.getUsedConstants.toList ++ pending
  for required in #[``StrandCanonicalExecution.rawReal,
      ``StrandCanonicalExperiments.rawSimulate,
      ``StrandCanonicalCommitmentHiding.commitment_hiding,
      ``StrandCanonicalExactSimulation.ghost_simulator_view,
      ``StrandCanonicalFullCoupling.complete_view,
      ``StrandCanonicalBackend.responseCoupling,
      ``FrontendCanonicalRows.frontendCoupling,
      ``MdocWitness.noninterference_of_readDisjoint] do
    unless visited.contains required do
      throwError "Complete privacy endpoint disconnected from {required}"
  for endpoint in #[``Mdoc.OracleWindow.leaves_subset,
      ``Mdoc.OracleWindow.leafWindow_domain,
      ``Mdoc.OracleWindow.values_extend,
      ``Mdoc.OracleWindow.values_leafOracle,
      ``Mdoc.OracleWindow.metadata_extend,
      ``Mdoc.SetupSupport.program_result,
      ``Mdoc.SetupSupport.values_congr,
      ``Mdoc.SetupSupport.metadata_actual,
      ``Mdoc.SetupSupport.runtime_actual,
      ``Mdoc.SetupSupport.metadata_congr,
      ``StrandPrivacyBudget.at_query_budget,
      ``MdocWitness.uniformHashValid_of_valid,
      ``Mdoc.ZeroKnowledge.honest,
      ``Mdoc.ZeroKnowledge.simulate,
      ``Mdoc.ZeroKnowledge.real_congr,
      ``Mdoc.ZeroKnowledge.simulate_congr,
      ``Mdoc.ZeroKnowledge.real_extend,
      ``Mdoc.ZeroKnowledge.simulate_extend,
      ``Mdoc.ZeroKnowledge.fixedComplement,
      ``Mdoc.ZeroKnowledge.statClose,
      ``Mdoc.ZeroKnowledge.statClose_at_query_budget,
      ``StrandVerifierObserver.observe_result,
      ``StrandVerifierObserver.optional_result,
      ``Mdoc.VerifierPrivacy.verifier_result,
      ``Mdoc.VerifierPrivacy.acceptance_probability] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeMdocStrandPrivacy
