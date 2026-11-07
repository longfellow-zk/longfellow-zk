import LfzkV2.Current.ZeroKnowledge.ObserverSupport
import LfzkV2.Current.ZeroKnowledge.ObserverExperiment
import LfzkV1.FromLigeroZKV1

/-! The observer's private context survives the proof phase. Only its
public request projection is passed to the protocol; the later query tree
receives the entire context. Reusing `Observer.View` with Context in its
request slot also makes that private state available to the observer's
final distinguishing predicate. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.ObserverStateful
open Merkle.RandomOracle LigeroFamily
open scoped Classical
variable {QM AM QT AT Context Request Proof Out : Type}
variable {preM preT postM postT : ℕ}
variable (requestOf : Context → Request)
variable (prior : TwoOracleTree QM AM QT AT Context preM preT)
variable (prove : Request → (QM → AM) → (QT → AT) → Proof × ((QM → AM) × (QT → AT)))
variable (after : Context → Proof → TwoOracleTree QM AM QT AT Out postM postT)

def callback (context : Context) := prove (requestOf context)

def experiment (HM : QM → AM) (HT : QT → AT) : Observer.View QM AM QT AT Context Proof Out :=
  Observer.experiment prior (callback requestOf prove) after HM HT

theorem context_eq (HM : QM → AM) (HT : QT → AT) :
    (experiment requestOf prior prove after HM HT).request = (Observer.run HM HT prior).1 := rfl

theorem public_request_eq (HM : QM → AM) (HT : QT → AT) :
    requestOf (experiment requestOf prior prove after HM HT).request = requestOf (Observer.run HM HT prior).1 := rfl

theorem identity (prior : TwoOracleTree QM AM QT AT Request preM preT)
    (after : Request → Proof → TwoOracleTree QM AM QT AT Out postM postT) (HM : QM → AM) (HT : QT → AT) :
    experiment id prior prove after HM HT = Observer.experiment prior prove after HM HT := rfl

def mapContext {Other : Type} (project : Context → Other)
    (view : Observer.View QM AM QT AT Context Proof Out) : Observer.View QM AM QT AT Other Proof Out where
  request := project view.request
  proof := view.proof
  before := view.before
  output := view.output
  after := view.after

section Support
variable [Fintype AM] [Fintype AT]

/-- Private contexts need not form a finite type. Restrict the original
prior tree to its derived finite support, then erase only the membership
proof from the final view. The execution and both query budgets agree. -/
theorem supported_experiment (HM : QM → AM) (HT : QT → AT) :
    mapContext Subtype.val
      (experiment (requestOf ∘ Subtype.val) (ObserverSupport.restrict prior) prove
        (fun context => after context.val) HM HT) =
      experiment requestOf prior prove after HM HT := by
  have same := ObserverSupport.restrict_run HM HT prior
  have context := congrArg Prod.fst same
  have trace := congrArg Prod.snd same
  simp only at context trace
  unfold experiment Observer.experiment callback mapContext
  simp only [Function.comp_apply]
  rw [context,trace]

theorem statClose_supported {R S : Type} [Fintype R] [Fintype S]
    {epsilon : ℚ} (realHM : R → QM → AM) (simulateHM : S → QM → AM)
    (realHT : R → QT → AT) (simulateHT : S → QT → AT)
    (real : R → Request → (QM → AM) → (QT → AT) → Proof × ((QM → AM) × (QT → AT)))
    (simulate : S → Request → (QM → AM) → (QT → AT) → Proof × ((QM → AM) × (QT → AT)))
    (finite : StatClose epsilon
      (fun coin => experiment (requestOf ∘ Subtype.val) (ObserverSupport.restrict prior) (real coin)
        (fun context => after context.val) (realHM coin) (realHT coin))
      (fun coin => experiment (requestOf ∘ Subtype.val) (ObserverSupport.restrict prior) (simulate coin)
        (fun context => after context.val) (simulateHM coin) (simulateHT coin))) :
    StatClose epsilon
      (fun coin => experiment requestOf prior (real coin) after (realHM coin) (realHT coin))
      (fun coin => experiment requestOf prior (simulate coin) after (simulateHM coin) (simulateHT coin)) := by
  have mapped := statClose_map (mapContext (QM := QM) (AM := AM) (QT := QT) (AT := AT)
    (Proof := Proof) (Out := Out) Subtype.val) finite
  simpa only [supported_experiment] using mapped

end Support
end LfzkV2.Current.ZeroKnowledge.ObserverStateful
