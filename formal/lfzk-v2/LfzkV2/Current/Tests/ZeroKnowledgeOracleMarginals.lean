import LfzkV2.Current.ZeroKnowledge.SHAOracleWindowProbability
import LfzkV2.Current.ZeroKnowledge.MdocSetupFamily
import LfzkV2.Current.ZeroKnowledge.ObserverFamilySupport
import LfzkV2.Current.ZeroKnowledge.TranscriptGlobalWindow

noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgeOracleMarginals
open Merkle.RandomOracle ZeroKnowledge

/-- Different public setups may select different private states. The
ambient state space remains infinite, while one common support suffices. -/
def prior (visible : Bool) : TwoOracleTree ℕ Bool ℕ Bool ℕ 1 0 :=
  .queryLeft 0 fun answer => .done (if visible then (if answer then 17 else 29) else 43)

example : Fintype (ObserverFamilySupport.Support prior) := inferInstance

example :
    ((Observer.run (fun _ => true) (fun _ => false)
      (ObserverFamilySupport.restrict prior true)).1.val,
      (Observer.run (fun _ => true) (fun _ => false)
        (ObserverFamilySupport.restrict prior true)).2) =
      Observer.run (fun _ => true) (fun _ => false) (prior true) :=
  ObserverFamilySupport.restrict_run prior true _ _

#print axioms SHAOracleWindowProbability.window_statClose
#print axioms MdocSetupFamily.setup_values
#print axioms MdocSetupFamily.values_merge
#print axioms ObserverFamilySupport.restrict_run
#print axioms ObserverFamilySupport.supported_experiment
#print axioms TranscriptGlobalWindow.canonical_mem
#print axioms TranscriptGlobalWindow.after_subset
#print axioms TranscriptGlobalWindow.observer_subset

end LfzkV2.Current.Tests.ZeroKnowledgeOracleMarginals
