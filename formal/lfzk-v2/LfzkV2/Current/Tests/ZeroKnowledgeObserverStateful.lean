import LfzkV2.Current.ZeroKnowledge.ObserverStatefulRaw

noncomputable section

/-! A private state with an infinite ambient type controls later queries
even when the public request is constant. Its finite analysis support is
derived from the earlier bounded program. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeObserverStateful
open Merkle.RandomOracle ZeroKnowledge

def prior : TwoOracleTree ℕ Bool ℕ Bool ℕ 1 0 :=
  .queryLeft 0 fun answer => .done (if answer then 37 else 99)

def after (context : ℕ) (_proof : Unit) : TwoOracleTree ℕ Bool ℕ Bool Bool 0 1 :=
  .queryRight context fun answer => .done answer

def prove (_request : Unit) (HM HT : ℕ → Bool) := ((),(HM,HT))

example : Fintype (ObserverSupport.Support prior) := inferInstance

example :
    (ObserverStateful.experiment (fun _ : ℕ => ()) prior prove after (fun _ => true) (fun _ => false)).after =
      [Sum.inr (37,false)] := rfl

example :
    (ObserverStateful.experiment (fun _ : ℕ => ()) prior prove after (fun _ => false) (fun _ => false)).after =
      [Sum.inr (99,false)] := rfl

/-- The finite support can contain inconsistent paths: the same query
cannot return two different answers in an actual oracle execution. Witness
validity must therefore stay scoped to executions, rather than this support. -/
def repeatedPrior : TwoOracleTree ℕ Bool ℕ Bool ℕ 2 0 :=
  .queryLeft 7 fun first => .queryLeft 7 fun second => .done (if first = second then 37 else 99)

example : 99 ∈ ObserverSupport.outputs repeatedPrior := by
  simp [repeatedPrior,ObserverSupport.outputs]

example (HM HT : ℕ → Bool) : (Observer.run HM HT repeatedPrior).1 = 37 := by
  simp [repeatedPrior,Observer.run]

#print axioms Observer.map_run
#print axioms Observer.record_run
#print axioms ObserverSupport.run_mem
#print axioms ObserverSupport.restrict_run
#print axioms ObserverStateful.supported_experiment
#print axioms ObserverStateful.statClose_supported
#print axioms ObserverStatefulRaw.rawRun_eq_execution
#print axioms ObserverStatefulRaw.projection
#print axioms ObserverStatefulRaw.experiment_view
#print axioms ObserverStatefulRaw.statClose
#print axioms ObserverStatefulRaw.supported_rawRun

end LfzkV2.Current.Tests.ZeroKnowledgeObserverStateful
