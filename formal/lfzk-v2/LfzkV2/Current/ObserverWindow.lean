import LfzkV2.Current.OracleWindow
import LfzkV2.Current.Observer

/-! Finite oracle windows for a mixed adaptive observer. Restriction
preserves the complete original output and both query traces. -/
noncomputable section
namespace LfzkV2.Current.ObserverWindow
open Merkle.RandomOracle Finset
open scoped Classical

variable {Raw D QT AT Value : Type}
variable [Fintype D] [Fintype AT] [DecidableEq Raw]

def mixedQueries : {left right : ℕ} → TwoOracleTree Raw D QT AT Value left right → Finset Raw
  | _,_,.done _ => ∅
  | _,_,.queryLeft query next => insert query (univ.biUnion fun answer => mixedQueries (next answer))
  | _,_,.queryRight _ next => univ.biUnion fun answer => mixedQueries (next answer)

def restrictMixed (window : Finset Raw) : {left right : ℕ} →
    (tree : TwoOracleTree Raw D QT AT Value left right) → mixedQueries tree ⊆ window →
      TwoOracleTree {raw // raw ∈ window} D QT AT Value left right
  | _,_,.done value,_ => .done value
  | _,_,.queryLeft query next,contains =>
      .queryLeft ⟨query,contains (mem_insert_self _ _)⟩ fun answer =>
        restrictMixed window (next answer) fun _ member =>
          contains (mem_insert_of_mem (mem_biUnion.mpr ⟨answer,mem_univ _,member⟩))
  | _,_,.queryRight query next,contains =>
      .queryRight query fun answer => restrictMixed window (next answer) fun _ member =>
        contains (mem_biUnion.mpr ⟨answer,mem_univ _,member⟩)

def liftEvent (window : Finset Raw) :
    ({raw // raw ∈ window} × D) ⊕ (QT × AT) → (Raw × D) ⊕ (QT × AT)
  | .inl qa => .inl (qa.1.val,qa.2)
  | .inr qa => .inr qa

theorem restrictMixed_run (window : Finset Raw) {left right : ℕ}
    (tree : TwoOracleTree Raw D QT AT Value left right) (contains : mixedQueries tree ⊆ window)
    (HM : Raw → D) (HT : QT → AT) :
    ((Observer.run (fun raw => HM raw.val) HT (restrictMixed window tree contains)).1,
      (Observer.run (fun raw => HM raw.val) HT (restrictMixed window tree contains)).2.map
        (liftEvent window)) = Observer.run HM HT tree := by
  induction tree with
  | done value => rfl
  | queryLeft query next ih =>
      simp only [restrictMixed,Observer.run,List.map_cons,liftEvent]
      have tail := ih (HM query) (fun _ member =>
        contains (mem_insert_of_mem (mem_biUnion.mpr ⟨HM query,mem_univ _,member⟩)))
      have output := congrArg Prod.fst tail
      have trace := congrArg Prod.snd tail
      exact Prod.ext output (congrArg (List.cons (.inl (query,HM query))) trace)
  | queryRight query next ih =>
      simp only [restrictMixed,Observer.run,List.map_cons,liftEvent]
      have tail := ih (HT query) (fun _ member =>
        contains (mem_biUnion.mpr ⟨HT query,mem_univ _,member⟩))
      have output := congrArg Prod.fst tail
      have trace := congrArg Prod.snd tail
      exact Prod.ext output (congrArg (List.cons (.inr (query,HT query))) trace)

theorem restrictMixed_extend_run (window : Finset Raw) {left right : ℕ}
    (tree : TwoOracleTree Raw D QT AT Value left right) (contains : mixedQueries tree ⊆ window)
    (HM : {raw // raw ∈ window} → D) (outside : Raw → D) (HT : QT → AT) :
    ((Observer.run HM HT (restrictMixed window tree contains)).1,
      (Observer.run HM HT (restrictMixed window tree contains)).2.map (liftEvent window)) =
      Observer.run (OracleWindow.extend window HM outside) HT tree := by
  have values : (fun raw : {raw // raw ∈ window} => OracleWindow.extend window HM outside raw.val) = HM := by
    funext raw
    simp only [OracleWindow.extend,raw.property,↓reduceDIte]
  simpa only [values] using restrictMixed_run window tree contains (OracleWindow.extend window HM outside) HT

private theorem queries_left_record {left right : ℕ}
    (HT : QT → AT) (tree : TwoOracleTree Raw D QT AT Value left right)
    (past : List (Observer.Event (QM := Raw) (AM := D) (QT := QT) (AT := AT))) :
    OracleWindow.queries (TranscriptV2.Memoize.left HT (Observer.record past tree)) ⊆ mixedQueries tree := by
  induction tree generalizing past with
  | done value => exact empty_subset _
  | queryLeft query next ih =>
      intro raw member
      simp only [TranscriptV2.Memoize.left,Observer.record,OracleWindow.queries,mem_insert] at member
      rcases member with same | member
      · exact mem_insert.mpr (Or.inl same)
      · obtain ⟨answer,_,member⟩ := mem_biUnion.mp member
        exact mem_insert_of_mem (mem_biUnion.mpr ⟨answer,mem_univ _,ih answer _ member⟩)
  | queryRight query next ih =>
      intro raw member
      exact mem_biUnion.mpr ⟨HT query,mem_univ _,ih (HT query) _ member⟩

/-- A residual for any fixed transcript oracle queries only coordinates
already included by the original mixed observer's all-branches window. This
holds for the programmed oracle returned by the simulator as well. -/
theorem queries_fixTranscript_subset {left right : ℕ} (HT : QT → AT)
    (tree : TwoOracleTree Raw D QT AT Value left right) :
    OracleWindow.queries (Observer.fixTranscript HT tree) ⊆ mixedQueries tree :=
  queries_left_record HT tree []

end LfzkV2.Current.ObserverWindow
