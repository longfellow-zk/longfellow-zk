import LfzkV2.Current.ZeroKnowledge.MerkleCommitLabels
import LfzkV2.Current.ZeroKnowledge.MerkleCache

/-! The causal honest-commitment refresh is the prepared-oracle experiment.
All freshness premises are derived from independently sampled commitment
inputs and the earlier observer's actual trace. The final table retains
every other oracle coordinate, including the observer's prior answers. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh

open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Enc Request : Type}
variable [Inhabited Digest]
variable (n : ℕ) (codec : Codec Salt Message Digest Enc)
variable (nonce : Request → Fin n → Salt) (cells : Request → Fin n → Message)

theorem sampledRun_trace_mem (request : Request) (tape : Fin (2*n-1) → Digest)
    (trace : List (Enc × Digest)) (count : ℕ) (fits : count ≤ 2*n-1) (qa : Enc × Digest) :
    qa ∈ (MerkleRefresh.sampledRun (input codec n nonce cells) (update n)
      ((request,fun _ => default),trace) tape count fits).2 ↔
      qa ∈ trace ∨ ∃ i : Fin (2*n-1), i.val < count ∧
        qa = (sampledInput n codec nonce cells request tape i,tape i) := by
  induction count with
  | zero => simp only [MerkleRefresh.sampledRun,Nat.not_lt_zero,false_and,exists_false,or_false]
  | succ count ih =>
      change qa ∈
        (MerkleRefresh.sampledRun (input codec n nonce cells) (update n)
          ((request,fun _ => default),trace) tape count (by omega)).2 ++
          [(input codec n nonce cells count
              (MerkleRefresh.sampledRun (input codec n nonce cells) (update n)
                ((request,fun _ => default),trace) tape count (by omega)).1,
            tape ⟨count,by omega⟩)] ↔ _
      rw [List.mem_append,List.mem_singleton,ih,
        MerkleRefresh.sampledRun_state]
      change (qa ∈ trace ∨ ∃ i : Fin (2*n-1), i.val < count ∧
          qa = (sampledInput n codec nonce cells request tape i,tape i)) ∨
          qa = (sampledInput n codec nonce cells request tape ⟨count,by omega⟩,tape ⟨count,by omega⟩) ↔ _
      constructor
      · rintro ((prior | ⟨i,earlier,equal⟩) | equal)
        · exact Or.inl prior
        · exact Or.inr ⟨i,by omega,equal⟩
        · exact Or.inr ⟨⟨count,by omega⟩,by change count < count+1; omega,equal⟩
      · rintro (prior | ⟨i,earlier,equal⟩)
        · exact Or.inl (Or.inl prior)
        · by_cases previous : i.val < count
          · exact Or.inl (Or.inr ⟨i,previous,equal⟩)
          · have last : i = ⟨count,by omega⟩ := Fin.ext (by change i.val = count; omega)
            exact Or.inr (last ▸ equal)

variable [DecidableEq Enc]
variable {fuel : ℕ} (before : Tree Enc Digest Request fuel)

/-- No collision or prior hit in the independent-label experiment implies
every actual refresh step is fresh. There is no premise about the unknown
refreshed oracle's behavior. -/
theorem refresh_fresh (positive : 0 < n) (background : Enc → Digest)
    (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce (before.run background).1)
      (cells (before.run background).1)
      (commitOracle codec n (nonce (before.run background).1) (cells (before.run background).1) tape))
    (priorAvoids : ∀ qa ∈ (before.run background).2,
      qa.1 ∉ commitSeen codec n (nonce (before.run background).1) (cells (before.run background).1) tape) :
    ∀ i : Fin (2*n-1), MerklePrequery.fresh
      (MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) i.val)
      (input codec n nonce cells i.val)
      (MerkleRefresh.refresh (initial before) (input codec n nonce cells) (update n)
        i.val (Nat.le_of_lt i.isLt) (background,tape)).1 := by
  apply MerkleRefresh.fresh_of_sampled
  intro i qa member
  have prior : (initial before).run background =
      (((before.run background).1,fun _ => default),(before.run background).2) := by
    simp only [initial,Tree.run_map]
  rw [prior] at member ⊢
  rw [MerkleRefresh.sampledRun_state]
  change qa.1 ≠ sampledInput n codec nonce cells (before.run background).1 tape i
  rcases (sampledRun_trace_mem n codec nonce cells _ tape _ i.val (Nat.le_of_lt i.isLt) qa).mp member with
    old | ⟨j,earlier,equal⟩
  · intro same
    apply priorAvoids qa old
    rw [same]
    exact (mem_commitSeen_iff_sampledInput n codec nonce cells positive _ tape injective _).mpr ⟨i,rfl⟩
  · rw [equal]
    intro same
    have indices := sampledInput_injective n codec nonce cells positive _ tape injective same
    have values := congrArg Fin.val indices
    omega

theorem refresh_eq_prepared_of_injective (positive : 0 < n)
    (background : Enc → Digest) (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce (before.run background).1)
      (cells (before.run background).1)
      (commitOracle codec n (nonce (before.run background).1) (cells (before.run background).1) tape))
    (priorAvoids : ∀ qa ∈ (before.run background).2,
      qa.1 ∉ commitSeen codec n (nonce (before.run background).1) (cells (before.run background).1) tape) :
    (MerkleRefresh.refresh (initial before) (input codec n nonce cells) (update n)
        (2*n-1) (le_refl _) (background,tape)).1 =
      MerkleCache.prepared codec n (nonce (before.run background).1)
        (cells (before.run background).1) tape background := by
  have unused := refresh_fresh n codec nonce cells before positive background tape injective priorAvoids
  funext query
  by_cases inside : query ∈ commitSeen codec n (nonce (before.run background).1) (cells (before.run background).1) tape
  · obtain ⟨i,rfl⟩ := (mem_commitSeen_iff_sampledInput n codec nonce cells positive _ tape injective query).mp inside
    rw [MerkleCache.prepared,if_pos inside,
      commitOracle_sampledInput n codec nonce cells positive _ tape injective i]
    have replay := MerkleRefresh.sampled_run (initial before) (input codec n nonce cells) (update n)
      (background,tape) (2*n-1) (le_refl _) unused
    have member : (sampledInput n codec nonce cells (before.run background).1 tape i,tape i) ∈
        ((MerkleRefresh.history (initial before) (input codec n nonce cells) (update n) (2*n-1)).run
          (MerkleRefresh.refresh (initial before) (input codec n nonce cells) (update n)
            (2*n-1) (le_refl _) (background,tape)).1).2 := by
      rw [replay]
      simp only [initial,Tree.run_map]
      exact (sampledRun_trace_mem n codec nonce cells _ tape _ _ (le_refl _) _).mpr
        (Or.inr ⟨i,i.isLt,rfl⟩)
    exact (Tree.trace_sound _ _ _ member).symm
  · rw [MerkleCache.prepared_outside codec n _ _ tape background query inside]
    apply MerkleRefresh.refresh_outside (initial before) (input codec n nonce cells) (update n)
      (background,tape) unused query _ (2*n-1) (le_refl _)
    intro i same
    apply inside
    have prior : ((initial before).run background).1 = ((before.run background).1,fun _ => default) := by
      simp only [initial,Tree.run_map]
    rw [prior] at same
    change query = sampledInput n codec nonce cells (before.run background).1 tape i at same
    exact (mem_commitSeen_iff_sampledInput n codec nonce cells positive _ tape injective query).mpr ⟨i,same.symm⟩

theorem refresh_eq_prepared (positive : 0 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest) (tape : Fin (2*n-1) → Digest)
    (noLeaves : ¬leafInputCollision codec n (nonce (before.run background).1) (cells (before.run background).1))
    (noLabels : ¬PairCollision (2*n-1) (slotPairs (2*n-1) (2*n-1)) tape)
    (noCross : ¬nodeInputHit codec n (nonce (before.run background).1) (cells (before.run background).1) tape)
    (priorAvoids : ∀ qa ∈ (before.run background).2,
      qa.1 ∉ commitSeen codec n (nonce (before.run background).1) (cells (before.run background).1) tape) :
    (MerkleRefresh.refresh (initial before) (input codec n nonce cells) (update n)
        (2*n-1) (le_refl _) (background,tape)).1 =
      MerkleCache.prepared codec n (nonce (before.run background).1)
        (cells (before.run background).1) tape background :=
  refresh_eq_prepared_of_injective n codec nonce cells before positive background tape
    (commitInputsInjective_of_no_tape_collision codec n positive
      (nonce (before.run background).1) (cells (before.run background).1) tape
      (le_refl _) codecInjective noLeaves noLabels noCross) priorAvoids

theorem priorAvoids_of_no_hit (positive : 0 < n) (background : Enc → Digest)
    (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce (before.run background).1)
      (cells (before.run background).1)
      (commitOracle codec n (nonce (before.run background).1) (cells (before.run background).1) tape))
    (noPriorLeaf : ∀ qa ∈ (before.run background).2, ∀ column : Fin n,
      qa.1 ≠ codec.leafEnc (nonce (before.run background).1 column,cells (before.run background).1 column))
    (noPriorNode : ∀ qa ∈ (before.run background).2, ∀ vertex : ℕ,
      0 < vertex → vertex < n → qa.1 ≠ tapeNodeInput codec n tape vertex) :
    ∀ qa ∈ (before.run background).2,
      qa.1 ∉ commitSeen codec n (nonce (before.run background).1) (cells (before.run background).1) tape := by
  intro qa member committed
  obtain ⟨i,same⟩ := (mem_commitSeen_iff_sampledInput n codec nonce cells positive _ tape injective qa.1).mp committed
  by_cases leaf : n ≤ 2*n-1-i.val
  · exact noPriorLeaf qa member ⟨2*n-1-i.val-n,by have := i.isLt; omega⟩
      (same.symm.trans (sampledInput_leaf n codec nonce cells _ tape i leaf))
  · have node : 2*n-1-i.val < n := by omega
    exact noPriorNode qa member (2*n-1-i.val) (by have := i.isLt; omega) node
      (same.symm.trans (sampledInput_node n codec nonce cells _ tape i node))

/-- Every endpoint premise is an explicitly counted independent-label bad
event: commitment collisions or a prior query guessing a nonce/child pair.
No oracle-refresh correspondence or stage-freshness certificate is supplied. -/
theorem refresh_eq_prepared_of_no_bad (positive : 0 < n) (codecInjective : codec.Inj)
    (background : Enc → Digest) (tape : Fin (2*n-1) → Digest)
    (noLeaves : ¬leafInputCollision codec n (nonce (before.run background).1) (cells (before.run background).1))
    (noLabels : ¬PairCollision (2*n-1) (slotPairs (2*n-1) (2*n-1)) tape)
    (noCross : ¬nodeInputHit codec n (nonce (before.run background).1) (cells (before.run background).1) tape)
    (noPriorLeaf : ∀ qa ∈ (before.run background).2, ∀ column : Fin n,
      qa.1 ≠ codec.leafEnc (nonce (before.run background).1 column,cells (before.run background).1 column))
    (noPriorNode : ∀ qa ∈ (before.run background).2, ∀ vertex : ℕ,
      0 < vertex → vertex < n → qa.1 ≠ tapeNodeInput codec n tape vertex) :
    (MerkleRefresh.refresh (initial before) (input codec n nonce cells) (update n)
        (2*n-1) (le_refl _) (background,tape)).1 =
      MerkleCache.prepared codec n (nonce (before.run background).1)
        (cells (before.run background).1) tape background := by
  have injective := commitInputsInjective_of_no_tape_collision codec n positive
    (nonce (before.run background).1) (cells (before.run background).1) tape
    (le_refl _) codecInjective noLeaves noLabels noCross
  exact refresh_eq_prepared n codec nonce cells before positive codecInjective background tape
    noLeaves noLabels noCross
    (priorAvoids_of_no_hit n codec nonce cells before positive background tape injective noPriorLeaf noPriorNode)

end LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh
