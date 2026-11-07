import LfzkV2.Current.ZeroKnowledge.ObserverExperiment

/-! Both oracle families occur before and after the proof. The later
observer must see both returned tables, including when both were changed. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeObserver
open Merkle.RandomOracle ZeroKnowledge

def prior : TwoOracleTree Unit Bool Unit Bool (Bool × Bool) 1 1 :=
  .queryLeft () fun merkle => .queryRight () fun transcript => .done (merkle,transcript)

def prove (_request : Bool × Bool) (_HM _HT : Unit → Bool) :
    Unit × ((Unit → Bool) × (Unit → Bool)) :=
  ((),(fun _ => false,fun _ => true))

def after (_request : Bool × Bool) (_proof : Unit) :
    TwoOracleTree Unit Bool Unit Bool (Bool × Bool) 1 1 :=
  .queryRight () fun transcript => .queryLeft () fun merkle => .done (merkle,transcript)

example : Observer.experiment prior prove after (fun _ => true) (fun _ => false) =
    (⟨(true,false),(),[.inl ((),true),.inr ((),false)],
      (false,true),[.inr ((),true),.inl ((),false)]⟩ :
      Observer.View Unit Bool Unit Bool (Bool × Bool) Unit (Bool × Bool)) := rfl

example : ((Observer.fixTranscript (fun _ : Unit => false) prior).run (fun _ => true)).1 =
    ((true,false),[.inl ((),true),.inr ((),false)]) := rfl

example : ((Observer.fixMerkle (fun _ : Unit => true) prior).run (fun _ => false)).1 =
    ((true,false),[.inl ((),true),.inr ((),false)]) := rfl

#print axioms Observer.fixTranscript_run
#print axioms Observer.fixMerkle_run
#print axioms Observer.typedTranscript_run
#print axioms Observer.full_conditionings_agree

end LfzkV2.Current.Tests.ZeroKnowledgeObserver
