import LfzkV2.Current.ZeroKnowledge.StrandCanonicalHiding
import LfzkV2.Current.ZeroKnowledge.MerkleBound
import Lean.Util.CollectAxioms

/-! The fixed-configuration canonical ZK composition retains actual raw
observer traces. Its probability bound is proved from nonce hiding and an
exact coin bijection; no execution certificate is an API premise. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalHiding
open ZeroKnowledge

#check StrandCanonicalBackend.complete_prepared
#check StrandCanonicalBackend.disclosed_respondHonest
#check StrandCanonicalExecution.stage_eq
#check StrandCanonicalCommitmentHiding.ghost_eq
#check StrandCanonicalCommitmentHiding.commitment_hiding
#check StrandCanonicalExactSimulation.simulationEquiv
#check StrandCanonicalExactSimulation.ghost_simulator_view
#check StrandCanonicalExactSimulation.ghost_sameDistribution
#check StrandCanonicalExactSimulation.exact_simulation
#check StrandCanonicalHiding.statClose

-- The concrete denominator is tied to the runtime's nonce-width constant.
example : Fintype.card MerkleNonce = 2^256 := MerkleSimulation.nonce_card

open Lean Elab Command in
run_cmd do
  for endpoint in #[``StrandCanonicalBackend.complete_prepared,
      ``StrandCanonicalBackend.disclosed_respondHonest,
      ``StrandCanonicalExecution.stage_eq,
      ``StrandCanonicalCommitmentHiding.ghost_eq,
      ``StrandCanonicalCommitmentHiding.commitment_hiding,
      ``StrandCanonicalExactSimulation.ghost_simulator_view,
      ``StrandCanonicalExactSimulation.ghost_sameDistribution,
      ``StrandCanonicalExactSimulation.exact_simulation,
      ``StrandCanonicalHiding.statClose] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalHiding
