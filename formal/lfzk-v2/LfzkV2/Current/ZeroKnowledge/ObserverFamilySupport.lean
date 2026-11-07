import LfzkV2.Current.ZeroKnowledge.ObserverStateful

/-! A finite family of public setups may choose different observer programs.
Their private outputs share one derived finite support, even when the original
private-state type is infinite. Only this proof-side enumeration is changed. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.ObserverFamilySupport
open Merkle.RandomOracle Finset
open scoped Classical
variable {QM AM QT AT Public Context Request Proof Out : Type}
variable [Fintype AM] [Fintype AT] [Fintype Public]
variable {preM preT postM postT : ℕ}
variable (prior : Public → TwoOracleTree QM AM QT AT Context preM preT)

@[irreducible] def outputs : Finset Context := univ.biUnion fun visible => ObserverSupport.outputs (prior visible)

abbrev Support := {context // context ∈ outputs prior}

instance : Fintype (Support prior) := inferInstance

def restrict (visible : Public) : TwoOracleTree QM AM QT AT (Support prior) preM preT :=
  Observer.map
    (fun context : ObserverSupport.Support (prior visible) =>
      (⟨context.val,by rw [outputs]; exact mem_biUnion.mpr ⟨visible,mem_univ _,context.property⟩⟩ : Support prior))
    (ObserverSupport.restrict (prior visible))

theorem restrict_run (visible : Public) (HM : QM → AM) (HT : QT → AT) :
    ((Observer.run HM HT (restrict prior visible)).1.val,(Observer.run HM HT (restrict prior visible)).2) =
      Observer.run HM HT (prior visible) := by
  simpa only [restrict,Observer.map_run] using ObserverSupport.restrict_run HM HT (prior visible)

variable (requestOf : Public → Context → Request)
variable (prove : Public → Request → (QM → AM) → (QT → AT) → Proof × ((QM → AM) × (QT → AT)))
variable (after : Public → Context → Proof → TwoOracleTree QM AM QT AT Out postM postT)

theorem supported_experiment (visible : Public) (HM : QM → AM) (HT : QT → AT) :
    ObserverStateful.mapContext Subtype.val
      (ObserverStateful.experiment (requestOf visible ∘ Subtype.val) (restrict prior visible) (prove visible)
        (fun context => after visible context.val) HM HT) =
      ObserverStateful.experiment (requestOf visible) (prior visible) (prove visible) (after visible) HM HT := by
  have same := restrict_run prior visible HM HT
  have context := congrArg Prod.fst same
  have trace := congrArg Prod.snd same
  dsimp only at context trace
  unfold ObserverStateful.experiment Observer.experiment ObserverStateful.callback ObserverStateful.mapContext
  simp only [Function.comp_apply]
  rw [context,trace]

end LfzkV2.Current.ZeroKnowledge.ObserverFamilySupport
