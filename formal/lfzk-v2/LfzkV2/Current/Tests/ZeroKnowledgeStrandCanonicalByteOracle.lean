import LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteOracle
import Lean.Util.CollectAxioms

/-! The shared byte-oracle theorem uses derived all-branch support, rather
than an execution certificate or a caller-supplied support premise. These
checks also cover both deterministic support equalities and the generic
uniform-table lift used by the endpoint. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalByteOracle
open ZeroKnowledge

open Lean Elab Command in
run_cmd do
  for endpoint in #[``StrandLeafWindow.statClose,
      ``StrandReadWindow.agree_of_window,
      ``StrandMerkleWindow.commitLabels_congr,
      ``StrandMerkleWindow.openCore_congr,
      ``StrandObserverWindow.before_congr,
      ``StrandObserverWindow.after_congr,
      ``StrandCanonicalBackend.fullView_congr_reads,
      ``StrandCanonicalByteSupport.rawReal_congr,
      ``StrandCanonicalByteSupport.rawSimulate_congr,
      ``StrandCanonicalByteOracle.real_extend,
      ``StrandCanonicalByteOracle.simulate_extend,
      ``StrandCanonicalByteOracle.statClose] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"

end LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalByteOracle
