import LfzkV2.Current.ZeroKnowledge.MdocStrandVerifierPrivacy
import Lean.Util.CollectAxioms

/-! The numbered-strand endpoint derives setup and raw support internally,
and its acceptance observer is the actual indexed runtime verifier. Guard
all new bridges as well as the complete privacy and concrete-budget results. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocStrandPrivacy
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for endpoint in #[``MdocStrandZeroKnowledge.statClose,
      ``MdocStrandVerifierPrivacy.acceptance_probability] do
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
    unless used.contains ``MdocStrandZeroKnowledge.Reachable &&
        used.contains ``MdocWitness.ReadDisjoint && used.contains ``MdocWitness.HashValid do
      throwError "Endpoint {endpoint} lost reached-witness or static-circuit premises"
    if used.contains ``MdocWitness.UniformHashValid then
      throwError "Endpoint {endpoint} exposes the derived uniform witness premise"
  for endpoint in #[``StrandMdocSetup.leaves_subset,
      ``StrandMdocSetup.leafWindow_domain,
      ``StrandMdocSetup.values_extend,
      ``StrandMdocSetup.values_leafOracle,
      ``StrandMdocSetup.metadata_extend,
      ``StrandMdocSetupSupport.program_result,
      ``StrandMdocSetupSupport.values_congr,
      ``StrandMdocSetupSupport.metadata_actual,
      ``StrandMdocSetupSupport.metadata_congr,
      ``StrandPrivacyBudget.at_query_budget,
      ``MdocWitness.uniformHashValid_of_valid,
      ``MdocStrandZeroKnowledge.honest,
      ``MdocStrandZeroKnowledge.simulate,
      ``MdocStrandZeroKnowledge.real_congr,
      ``MdocStrandZeroKnowledge.simulate_congr,
      ``MdocStrandZeroKnowledge.real_extend,
      ``MdocStrandZeroKnowledge.simulate_extend,
      ``MdocStrandZeroKnowledge.fixedComplement,
      ``MdocStrandZeroKnowledge.statClose,
      ``MdocStrandZeroKnowledge.statClose_at_query_budget,
      ``StrandVerifierObserver.observe_result,
      ``StrandVerifierObserver.optional_result,
      ``MdocStrandVerifierPrivacy.verifier_result,
      ``MdocStrandVerifierPrivacy.acceptance_probability] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeMdocStrandPrivacy
