import TranscriptV2.StrandCoupling

/-! Split the coupled execution at proof submission. Verifier replay resumes
the same node and stream cache; it cannot obtain a second fresh answer for a
query already made by the prover. The state here belongs to the proof model
and is never exposed by the transcript API. -/
noncomputable section
namespace TranscriptV2.StrandCoupling
open Merkle.RandomOracle

variable {P K D I Out Result : Type} [DecidableEq P] [DecidableEq K]

variable (streamKey : P → D → K)

/-- Retain the sampling cache at the submission cut. Erasing this cache
gives exactly the eager coupling already used for the probability law. -/
def eagerState (streamKey : P → D → K) : {fuel : ℕ} → Tree (Point P K I) D Out fuel → Cache P K D I →
    Tree (SamplePoint P K) (Sample D I) (Out × Cache P K D I) fuel
  | _, .done output, state => .done (output,state)
  | _, .query (.inl point) next, state =>
      match state.nodes point with
      | some digest => (eagerState streamKey (next digest) state).weaken
      | none => .query (.inl point) fun answer =>
          let updated := state.node point answer.1
          let reserved := match state.streams (streamKey point answer.1) with
            | some _ => updated
            | none => updated.stream (streamKey point answer.1) answer.2
          eagerState streamKey (next answer.1) reserved
  | _, .query (.inr (digest,counter)) next, state =>
      match state.streams digest with
      | some bytes => (eagerState streamKey (next (bytes counter)) state).weaken
      | none => .query (.inr digest) fun answer =>
          eagerState streamKey (next (answer.2 counter)) (state.stream digest answer.2)

private theorem map_weaken {X Y Z W : Type} {fuel : ℕ}
    (tree : Tree X Y Z fuel) (f : Z → W) : tree.weaken.map f = (tree.map f).weaken := by
  induction tree with
  | done output => rfl
  | query point next ih => exact congrArg (Tree.query point) (funext ih)

theorem eagerState_map {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (f : Out → Result) (state : Cache P K D I) :
    eagerState streamKey (program.map f) state = (eagerState streamKey program state).map (Prod.map f id) := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simp only [Merkle.RandomOracle.Tree.map,eagerState,found,map_weaken,ih]
          | none => simp only [Merkle.RandomOracle.Tree.map,eagerState,found,ih]
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simp only [Merkle.RandomOracle.Tree.map,eagerState,found,map_weaken,ih]
          | none => simp only [Merkle.RandomOracle.Tree.map,eagerState,found,ih]

theorem eagerState_forget {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) :
    (eagerState streamKey program state).map Prod.fst = eagerTree streamKey program state := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simp only [eagerState,eagerTree,found,map_weaken,ih]
          | none =>
              simp only [eagerState,eagerTree,found,Merkle.RandomOracle.Tree.map,ih]
              rfl
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simp only [eagerState,eagerTree,found,map_weaken,ih]
          | none => simp only [eagerState,eagerTree,found,Merkle.RandomOracle.Tree.map,ih]

theorem eagerState_erases {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    (((eagerState streamKey program state).run H).1.1,((eagerState streamKey program state).run H).2) =
      (eagerTree streamKey program state).run H := by
  rw [← eagerState_forget,Tree.run_map]

theorem eagerState_fresh {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) : FreshOracle.FreshFrom state.known (eagerState streamKey program state) := by
  apply FreshOracle.FreshFrom.of_map Prod.fst
  rw [eagerState_forget]
  exact eagerTree_fresh streamKey program state

private theorem bind_weaken {X Y Z W : Type} {fuel extra : ℕ}
    (tree : Tree X Y Z fuel) (next : Z → Tree X Y W extra) :
    tree.weaken.bind next = (tree.bind next).weaken := by
  induction tree with
  | done output => rfl
  | query point child ih => exact congrArg (Tree.query point) (funext ih)

theorem eagerState_weaken_tree {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) :
    eagerState streamKey program.weaken state = (eagerState streamKey program state).weaken := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point <;> simp only [Tree.weaken,eagerState,found,ih]
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest <;> simp only [Tree.weaken,eagerState,found,ih]

theorem eagerState_weakenAdd_tree {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (extra : ℕ) (state : Cache P K D I) :
    eagerState streamKey (program.weakenAdd extra) state = (eagerState streamKey program state).weakenAdd extra := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [Tree.weakenAdd,eagerState_weaken_tree,ih,Tree.weakenAdd]

/-- The coupling commutes with submission and replay as query programs,
so subsequent online naming may be applied to either side. -/
theorem eagerState_comp {fuel extra : ℕ} (program : Tree (Point P K I) D Out fuel)
    (replay : Out → Tree (Point P K I) D Result extra) (state : Cache P K D I) :
    eagerState streamKey (program.bind replay) state =
      (eagerState streamKey program state).bind fun cut => eagerState streamKey (replay cut.1) cut.2 := by
  induction program generalizing state with
  | done output => exact eagerState_weakenAdd_tree streamKey _ _ _
  | query point next ih =>
      cases point with
      | inl point =>
          cases found : state.nodes point with
          | some digest => simp only [Tree.bind,eagerState,found,ih,bind_weaken]
          | none => simp only [Tree.bind,eagerState,found,ih]
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases found : state.streams digest with
          | some bytes => simp only [Tree.bind,eagerState,found,ih,bind_weaken]
          | none => simp only [Tree.bind,eagerState,found,ih]

theorem eagerState_weaken {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    (eagerState streamKey program.weaken state).run H = (eagerState streamKey program state).run H := by
  rw [eagerState_weaken_tree,Tree.run_weaken]

theorem eagerState_weakenAdd {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (extra : ℕ) (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    (eagerState streamKey (program.weakenAdd extra) state).run H = (eagerState streamKey program state).run H := by
  rw [eagerState_weakenAdd_tree,Tree.run_weakenAdd]

/-- Composition retains both the exact cut state and the concatenated
query trace. No replay-history or fresh-answer assumption is supplied. -/
theorem eagerState_bind {fuel extra : ℕ} (program : Tree (Point P K I) D Out fuel)
    (replay : Out → Tree (Point P K I) D Result extra)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) :
    (eagerState streamKey (program.bind replay) state).run H =
      ((eagerState streamKey program state).bind fun cut => eagerState streamKey (replay cut.1) cut.2).run H := by
  rw [eagerState_comp]

end TranscriptV2.StrandCoupling
