import LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh
import Merkle.Hiding

/-! Independent refresh coins use exactly the commitment's existing label
layout: vertex v receives slot 2n−1−v.  This is a description of the sampled
analysis experiment.  It does not give the honest prover future labels.

The input correspondence below connects that experiment to the existing
commitment collision events and the actual commitment input cache. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh

open Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {Salt Message Digest Enc Request : Type}
variable [Inhabited Digest]
variable (n : ℕ)

def sampledState (request : Request) (tape : Fin (2*n-1) → Digest)
    (count : ℕ) (fits : count ≤ 2*n-1) : State Request Digest :=
  MerkleRefresh.sampled (update n) (request,fun _ => default) tape count fits

theorem sampled_request (request : Request) (tape : Fin (2*n-1) → Digest)
    (count : ℕ) (fits : count ≤ 2*n-1) :
    (sampledState n request tape count fits).1 = request := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih (by omega)

theorem sampled_processed (request : Request) (tape : Fin (2*n-1) → Digest)
    (count : ℕ) (fits : count ≤ 2*n-1) (vertex : ℕ)
    (processed : 2*n-1-count < vertex) (inHeap : vertex < 2*n) :
    (sampledState n request tape count fits).2 vertex = tape ⟨2*n-1-vertex,by omega⟩ := by
  induction count with
  | zero => omega
  | succ count ih =>
      change Function.update
        (sampledState n request tape count (by omega)).2 (2*n-1-count)
          (tape ⟨count,by omega⟩) vertex = _
      by_cases same : vertex = 2*n-1-count
      · calc
          _ = tape ⟨count,by omega⟩ := by simp only [same,Function.update_self]
          _ = _ := by
            congr 1
            apply Fin.ext
            change count = 2*n-1-vertex
            omega
      · rw [Function.update_of_ne same]
        exact ih (by omega) (by omega)

theorem sampled_unprocessed (request : Request) (tape : Fin (2*n-1) → Digest)
    (count : ℕ) (fits : count ≤ 2*n-1) (vertex : ℕ)
    (outside : vertex ≤ 2*n-1-count ∨ 2*n ≤ vertex) :
    (sampledState n request tape count fits).2 vertex = default := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change Function.update
        (sampledState n request tape count (by omega)).2 (2*n-1-count)
          (tape ⟨count,by omega⟩) vertex = _
      rw [Function.update_of_ne (by omega)]
      exact ih (by omega) (by omega)

variable (codec : Codec Salt Message Digest Enc)
variable (nonce : Request → Fin n → Salt) (cells : Request → Fin n → Message)

def sampledInput (request : Request) (tape : Fin (2*n-1) → Digest) (i : Fin (2*n-1)) : Enc :=
  input codec n nonce cells i.val (sampledState n request tape i.val (Nat.le_of_lt i.isLt))

theorem sampledInput_leaf (request : Request) (tape : Fin (2*n-1) → Digest)
    (i : Fin (2*n-1)) (leaf : n ≤ 2*n-1-i.val) :
    sampledInput n codec nonce cells request tape i =
      codec.leafEnc (nonce request ⟨2*n-1-i.val-n,by have := i.isLt; omega⟩,
        cells request ⟨2*n-1-i.val-n,by have := i.isLt; omega⟩) := by
  have upper : 2*n-1-i.val < 2*n := by have := i.isLt; omega
  have inLeaf : n ≤ 2*n-1-i.val ∧ 2*n-1-i.val < 2*n := ⟨leaf,upper⟩
  simp only [sampledInput,input,dif_pos inLeaf,sampled_request]

theorem sampledInput_node (request : Request) (tape : Fin (2*n-1) → Digest)
    (i : Fin (2*n-1)) (node : 2*n-1-i.val < n) :
    sampledInput n codec nonce cells request tape i =
      tapeNodeInput codec n tape (2*n-1-i.val) := by
  let vertex := 2*n-1-i.val
  have positive : 0 < vertex := by dsimp [vertex]; have := i.isLt; omega
  have upper : vertex < n := node
  unfold sampledInput input
  rw [dif_neg (by change ¬(n ≤ vertex ∧ vertex < 2*n); omega)]
  rw [sampled_processed n request tape i.val (Nat.le_of_lt i.isLt)
      (2*vertex) (by omega) (by omega),
    sampled_processed n request tape i.val (Nat.le_of_lt i.isLt)
      (2*vertex+1) (by omega) (by omega)]
  unfold tapeNodeInput tapeAt
  rw [dif_pos (by omega),dif_pos (by omega)]
  congr 2
  congr 1
  apply Fin.ext
  change 2*n-1-(2*vertex+1) = 2*n-2-2*(2*n-1-i.val)
  dsimp only [vertex]
  omega

variable [DecidableEq Enc]

/-- Off the existing collision events, independently sampled inputs are
exactly the inputs seen in the canonical lazy commitment. -/
theorem sampledInput_commitInput (positive : 0 < n)
    (request : Request) (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce request) (cells request)
      (commitOracle codec n (nonce request) (cells request) tape)) (i : Fin (2*n-1)) :
    commitInput codec n (nonce request) (cells request)
        (commitOracle codec n (nonce request) (cells request) tape) (2*n-1-i.val) =
      some (sampledInput n codec nonce cells request tape i) := by
  let vertex := 2*n-1-i.val
  have bounds : 0 < vertex ∧ vertex < 2*n := by dsimp [vertex]; have := i.isLt; omega
  by_cases leaf : n ≤ vertex
  · rw [sampledInput_leaf n codec nonce cells request tape i leaf]
    exact dif_pos ⟨leaf,bounds.2⟩
  · have node : vertex < n := by omega
    have children (child : ℕ) (after : vertex < child) (inside : child < 2*n) :
        (sampledState n request tape i.val (Nat.le_of_lt i.isLt)).2 child =
          commitLabels (codec.withOracle (commitOracle codec n (nonce request) (cells request) tape))
            n (nonce request) (cells request) child := by
      rw [sampled_processed n request tape i.val (Nat.le_of_lt i.isLt) child after inside,
        commitLabels_eq_tape codec n positive (nonce request) (cells request) tape injective
          child (by omega) (by omega) (by omega)]
    unfold sampledInput input
    rw [dif_neg (by change ¬(n ≤ vertex ∧ vertex < 2*n); omega)]
    unfold commitInput
    rw [dif_neg (by omega),if_pos ⟨bounds.1,node⟩,
      ← children (2*vertex) (by omega) (by omega),
      ← children (2*vertex+1) (by omega) (by omega)]

theorem sampledInput_injective (positive : 0 < n)
    (request : Request) (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce request) (cells request)
      (commitOracle codec n (nonce request) (cells request) tape)) :
    Function.Injective (sampledInput n codec nonce cells request tape) := by
  intro first second same
  by_contra different
  have bounds (i : Fin (2*n-1)) : 0 < 2*n-1-i.val ∧ 2*n-1-i.val < 2*n := by
    have := i.isLt
    omega
  have vertices : 2*n-1-first.val ≠ 2*n-1-second.val := by
    intro equal
    apply different
    apply Fin.ext
    have := first.isLt
    have := second.isLt
    omega
  apply injective (2*n-1-first.val) (2*n-1-second.val)
    (bounds first).1 (bounds first).2 (bounds second).1 (bounds second).2 vertices
    (sampledInput n codec nonce cells request tape first)
    (sampledInput_commitInput n codec nonce cells positive request tape injective first)
  rw [same]
  exact sampledInput_commitInput n codec nonce cells positive request tape injective second

/-- The endpoint premises are the explicitly counted commitment collision
events, rather than an unproved distinct-input certificate. -/
theorem sampledInput_injective_of_no_collision (positive : 0 < n) (codecInjective : codec.Inj)
    (request : Request) (tape : Fin (2*n-1) → Digest)
    (noLeaves : ¬leafInputCollision codec n (nonce request) (cells request))
    (noLabels : ¬PairCollision (2*n-1) (slotPairs (2*n-1) (2*n-1)) tape)
    (noCross : ¬nodeInputHit codec n (nonce request) (cells request) tape) :
    Function.Injective (sampledInput n codec nonce cells request tape) :=
  sampledInput_injective n codec nonce cells positive request tape
    (commitInputsInjective_of_no_tape_collision codec n positive (nonce request) (cells request)
      tape (le_refl _) codecInjective noLeaves noLabels noCross)

theorem mem_commitSeen_iff_sampledInput (positive : 0 < n)
    (request : Request) (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce request) (cells request)
      (commitOracle codec n (nonce request) (cells request) tape)) (query : Enc) :
    query ∈ commitSeen codec n (nonce request) (cells request) tape ↔
      ∃ i : Fin (2*n-1), sampledInput n codec nonce cells request tape i = query := by
  constructor
  · intro member
    obtain ⟨vertex,above,below,atVertex⟩ :=
      mem_commitSeen_vertex codec n (nonce request) (cells request) tape query member
    let i : Fin (2*n-1) := ⟨2*n-1-vertex,by omega⟩
    refine ⟨i,?_⟩
    have point := sampledInput_commitInput n codec nonce cells positive request tape injective i
    have back : 2*n-1-i.val = vertex := by dsimp [i]; omega
    rw [back,atVertex] at point
    exact (Option.some.inj point).symm
  · rintro ⟨i,rfl⟩
    exact mem_commitSeen_of_commitInput codec n positive (nonce request) (cells request) tape injective
      (2*n-1-i.val) (by have := i.isLt; omega) (by omega) _
      (sampledInput_commitInput n codec nonce cells positive request tape injective i)

/-- The prepared commitment table returns the very coin used at that
causal step, rather than merely an answer with the same distribution. -/
theorem commitOracle_sampledInput (positive : 0 < n)
    (request : Request) (tape : Fin (2*n-1) → Digest)
    (injective : commitInputsInjective codec n (nonce request) (cells request)
      (commitOracle codec n (nonce request) (cells request) tape)) (i : Fin (2*n-1)) :
    commitOracle codec n (nonce request) (cells request) tape
        (sampledInput n codec nonce cells request tape i) = tape i := by
  have slot := commitSeen_idxOf_eq codec n positive (nonce request) (cells request) tape injective
    (2*n-1-i.val) (by have := i.isLt; omega) (by omega) _
    (sampledInput_commitInput n codec nonce cells positive request tape injective i)
  have index : 2*n-1-(2*n-1-i.val) = i.val := by have := i.isLt; omega
  exact (congrArg (tapeAt tape default) (slot.trans index)).trans (dif_pos i.isLt)

end LfzkV2.Current.ZeroKnowledge.MerkleCommitRefresh
