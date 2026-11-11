import LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
import LfzkV2.Current.ZeroKnowledge.StrandCanonicalColumns
import LfzkV2.Current.ZeroKnowledge.RequestedPublic
import LfzkV2.Current.ZeroKnowledge.MdocWitnessFrontend
import LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability
import Lean.Util.CollectAxioms

/-! The reusable boundary for the remaining numbered-runtime composition.
These checks expose the existing pointwise frontend/backend equivalences,
actual canonical completion, and unchanged generic finite-window transport.
The exact coupled view is distinct from the real-to-ghost statistical hop. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalBridge
open LfzkV2.Current.ZeroKnowledge

#check Frontend.FullCoupling.sameDistribution
#check Backend.Adaptive.sameDistribution
#check StrandCanonicalBackend.respond
#check StrandCanonicalBackend.responseCoupling
#check StrandCanonicalBackend.backend_view
#check StrandCanonicalBackend.select
#check StrandCanonicalBackend.rawOpening
#check StrandCanonicalBackend.finish_valid
#check StrandCanonicalFullCoupling.simulatedView
#check StrandCanonicalFullCoupling.complete_view
#check StrandCanonicalBackend.respondHonest_columns
#check StrandCanonicalBackend.prepare_oracle_congr
#check RequestedSimulator.requestedBinary
#check RequestedSimulator.requestedPrime
#check RequestedSimulator.configuration
#check MdocWitness.coupling_hash
#check MdocWitness.honest_hash
#check SHAOracleWindowProbability.window_statClose

#print axioms Frontend.FullCoupling.sameDistribution
#print axioms Backend.Adaptive.sameDistribution
#print axioms StrandCanonicalBackend.respond
#print axioms StrandCanonicalBackend.backend_view
#print axioms StrandCanonicalBackend.finish_valid
#print axioms StrandCanonicalFullCoupling.complete_view
#print axioms MdocWitness.coupling_hash
#print axioms SHAOracleWindowProbability.window_statClose

-- Every implication in the concrete coin-change path is checked for
-- additional axioms, including the final exact distribution statement.
open Lean Elab Command in
run_cmd do
  for endpoint in #[``StrandCanonicalBackend.backend_view,
      ``StrandCanonicalBackend.respondHonest_columns,
      ``StrandCanonicalBackend.prepare_oracle_congr,
      ``StrandCanonicalFullCoupling.statementTruth,
      ``StrandCanonicalFullCoupling.complete_view,
      ``StrandCanonicalFullCoupling.sameDistribution] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalBridge
