import LfzkV2.Current.ZeroKnowledge.Observer

/-! A bounded observer has finitely many possible private outputs when
oracle answers are finite, even if its query and private-state types are
infinite. The finite support below may include inconsistent oracle paths;
it is used only for enumeration. Validity assumptions must still concern
actual executions, rather than every syntactic leaf. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.ObserverSupport
open Merkle.RandomOracle
open scoped Classical
variable {QM AM QT AT State Other : Type}

variable [Fintype AM] [Fintype AT]

def outputs : {left right : ℕ} → TwoOracleTree QM AM QT AT State left right → Finset State
  | _,_,.done value => {value}
  | _,_,.queryLeft _ next => Finset.univ.biUnion fun answer => outputs (next answer)
  | _,_,.queryRight _ next => Finset.univ.biUnion fun answer => outputs (next answer)

theorem run_mem (HM : QM → AM) (HT : QT → AT)
    {left right : ℕ} (tree : TwoOracleTree QM AM QT AT State left right) :
    (Observer.run HM HT tree).1 ∈ outputs tree := by
  induction tree with
  | done value => exact Finset.mem_singleton_self _
  | queryLeft query next ih =>
      exact Finset.mem_biUnion.mpr ⟨HM query,Finset.mem_univ _,ih (HM query)⟩
  | queryRight query next ih =>
      exact Finset.mem_biUnion.mpr ⟨HT query,Finset.mem_univ _,ih (HT query)⟩

abbrev Support {left right : ℕ} (tree : TwoOracleTree QM AM QT AT State left right) :=
  {state // state ∈ outputs tree}

instance supportFintype {left right : ℕ} (tree : TwoOracleTree QM AM QT AT State left right) :
    Fintype (Support tree) := inferInstance

/-- Restrict only the returned private state. Every actual query, answer,
branch and budget is retained. -/
def restrict : {left right : ℕ} → (tree : TwoOracleTree QM AM QT AT State left right) →
    TwoOracleTree QM AM QT AT (Support tree) left right
  | _,_,.done value => .done ⟨value,Finset.mem_singleton_self _⟩
  | _,_,.queryLeft query next => .queryLeft query fun answer =>
      Observer.map (fun value : Support (next answer) =>
        (⟨value.val,Finset.mem_biUnion.mpr ⟨answer,Finset.mem_univ _,value.property⟩⟩ :
          Support (.queryLeft query next))) (restrict (next answer))
  | _,_,.queryRight query next => .queryRight query fun answer =>
      Observer.map (fun value : Support (next answer) =>
        (⟨value.val,Finset.mem_biUnion.mpr ⟨answer,Finset.mem_univ _,value.property⟩⟩ :
          Support (.queryRight query next))) (restrict (next answer))

theorem restrict_run (HM : QM → AM) (HT : QT → AT)
    {left right : ℕ} (tree : TwoOracleTree QM AM QT AT State left right) :
    ((Observer.run HM HT (restrict tree)).1.val,(Observer.run HM HT (restrict tree)).2) =
      Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      simp only [restrict,Observer.run,Observer.map_run]
      exact congrArg (fun result : State × List (Observer.Event (QM := QM) (AM := AM) (QT := QT) (AT := AT)) =>
        (result.1,Sum.inl (query,HM query)::result.2)) (ih (HM query))
  | queryRight query next ih =>
      simp only [restrict,Observer.run,Observer.map_run]
      exact congrArg (fun result : State × List (Observer.Event (QM := QM) (AM := AM) (QT := QT) (AT := AT)) =>
        (result.1,Sum.inr (query,HT query)::result.2)) (ih (HT query))

end LfzkV2.Current.ZeroKnowledge.ObserverSupport
