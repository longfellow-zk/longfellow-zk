import LfzkV2.Current.ZeroKnowledge.FrontendCompleteTranscript
import LfzkV2.Current.ZeroKnowledge.MerklePrequery
import Merkle.TreeCompose

/-! The honest opening boundary is reached by a causal query tree, not by
replaying a complete H-dependent proof as if it were fixed. Each ordinary
step receives only the current state and one whole oracle answer. Its link
and challenge block therefore come from the same evaluation.

The indexed state makes the query bound and stopping boundary structural.
Every internally generated query has smaller rank than the opening query.
Only an observer's external prior queries can have guessed that last input.
The public refresh theorem consequently applies to the whole opening answer
on the honest path, before any fixed-Q backend masking equivalence is used. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRefresh
open Merkle.RandomOracle
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
local notation "State" => Frontend.CompleteTranscript.State g fields Advice Key Base C
local notation "Fresh" => ProtocolWrites.Fresh g fields Advice
local notation "Point" => Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)

abbrev At (rank : ℕ) := {state : Frontend.CompleteTranscript.State g fields Advice Key Base C // state.rank.val = rank}

def castAt {first second : ℕ} (equal : first = second)
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) first) :
    At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) second :=
  ⟨state.val,state.property.trans equal⟩

def initial (context : Key) (fallback : C) :
    At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) 0 :=
  ⟨Frontend.CompleteTranscript.initial context fallback,rfl⟩

variable (bindOnly : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
  (Fin i.val → C) → Base)

def prepare {rank : ℕ}
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (write : State → Fresh) :
    At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank :=
  ⟨Frontend.CompleteTranscript.bind state.val (fun _ => write state.val),state.property⟩

def query {rank : ℕ}
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (inside : rank < g.roles.length) : Point :=
  Frontend.CompleteTranscript.query bindOnly state.val (by rw [state.property]; exact inside)

@[simp] theorem query_rank {rank : ℕ}
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (inside : rank < g.roles.length) :
    (query (Authentication := Authentication) bindOnly state inside).rank = rank := state.property

def advance {rank : ℕ}
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (inside : rank < g.roles.length) (answer : Digest × C) :
    At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) (rank+1) :=
  ⟨Frontend.CompleteTranscript.advance bindOnly state.val (by rw [state.property]; exact inside) answer,
    congrArg (fun n => n+1) state.property⟩

/-- The local computation may inspect all already returned challenges and
private coins captured when the callback is fixed. It is not given an oracle
or an opening answer. The tree itself performs each subsequent query. -/
def runPrefix (write : State → Fresh) : (steps : ℕ) → {rank : ℕ} →
    rank+steps ≤ g.openingIndex.val →
    At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank →
    Tree Point (Digest × C)
      (At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) (rank+steps)) steps
  | 0,_,_,state => .done state
  | steps+1,rank,bound,state =>
      let pending := prepare state write
      let inside : rank < g.roles.length := by have := g.openingIndex.isLt; omega
      .query (query bindOnly pending inside) fun answer =>
        (runPrefix write steps (by omega) (advance bindOnly pending inside answer)).map
          (castAt (by omega))

/-- One compiled boundary is exactly the existing body-free reader step,
including feedback of that same answer's link. -/
theorem one_step (write : State → Fresh) (rank : ℕ) (bound : rank+1 ≤ g.openingIndex.val)
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (H : Point → Digest × C) :
    ((runPrefix bindOnly write 1 bound state).run H).1.val =
      (Frontend.CompleteTranscript.step bindOnly H (prepare state write).val).2 := by
  rw [Frontend.CompleteTranscript.step_query bindOnly H (prepare state write).val
    (by change state.val.rank.val < g.roles.length; rw [state.property]; have := g.openingIndex.isLt; omega)]
  rfl

/-- The complete internal prefix cannot query its own later opening input,
irrespective of the messages and earlier challenge values. -/
theorem prefix_queries_before (write : State → Fresh) (steps rank : ℕ)
    (bound : rank+steps ≤ g.openingIndex.val)
    (state : At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) rank)
    (H : Point → Digest × C) :
    ∀ qa ∈ ((runPrefix bindOnly write steps bound state).run H).2, qa.1.rank < g.openingIndex.val := by
  induction steps generalizing rank with
  | zero => simp only [runPrefix,Tree.run_done,List.not_mem_nil,false_implies,implies_true]
  | succ steps ih =>
      intro qa member
      simp only [runPrefix,Tree.run_query,Tree.run_map,List.mem_cons] at member
      rcases member with equal | member
      · subst qa
        rw [query_rank]
        omega
      · exact ih (rank+1) (by omega) _ qa member

variable {Request : Type} {fuel : ℕ}
variable (before : Tree (Frontend.CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
  (Authentication := Authentication) (Key := Key) (Base := Base)) (Digest × C) Request fuel)
variable (start : Request → At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) 0)
variable (writes openingWrites : Request → Frontend.CompleteTranscript.State g fields Advice Key Base C →
  ProtocolWrites.Fresh g fields Advice)

abbrev Finished := Request ×
  At (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) g.openingIndex.val

/-- Earlier observer queries may choose the request. The subsequent honest
rounds all share the same oracle and retain that full external trace. -/
def compile : Tree Point (Digest × C)
    (Finished (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base) (C := C) (Request := Request))
    (g.openingIndex.val+fuel) :=
  before.bind fun request =>
    (runPrefix bindOnly (writes request) g.openingIndex.val (by omega) (start request)).map fun state =>
      (request,castAt (Nat.zero_add _) state)

def opening (finished : Finished (g := g) (fields := fields) (Advice := Advice)
    (Key := Key) (Base := Base) (C := C) (Request := Request)) : Point :=
  query bindOnly (prepare finished.2 (openingWrites finished.1)) g.openingIndex.isLt

@[simp] theorem opening_rank (finished : Finished (g := g) (fields := fields) (Advice := Advice)
    (Key := Key) (Base := Base) (C := C) (Request := Request)) :
    (opening (Authentication := Authentication) bindOnly openingWrites finished).rank = g.openingIndex.val :=
  query_rank _ _ _

/-- All internal queries are excluded by their rank. The only remaining
bad event is a genuine external prior query of the complete opening input. -/
theorem fresh_iff_prior (H : Point → Digest × C) :
    MerklePrequery.fresh (compile bindOnly before start writes) (opening bindOnly openingWrites) H ↔
      ∀ qa ∈ (before.run H).2,
        qa.1 ≠ MerklePrequery.location (compile bindOnly before start writes) (opening bindOnly openingWrites) H := by
  unfold MerklePrequery.fresh
  rw [compile,Tree.run_bind]
  simp only [Tree.run_map,List.mem_append]
  constructor
  · intro fresh qa member
    exact fresh qa (Or.inl member)
  · intro prior qa member
    rcases member with member | member
    · exact prior qa member
    · intro equal
      have earlier := prefix_queries_before bindOnly (writes (before.run H).1)
        g.openingIndex.val 0 (by omega) (start (before.run H).1) H qa member
      have same := congrArg Input.rank equal
      have later := opening_rank (Authentication := Authentication) bindOnly openingWrites
        ((compile bindOnly before start writes).run H).1
      unfold MerklePrequery.location at same
      have equalRank := same.trans later
      omega

/-- Refreshing the honest last answer is one genuine oracle-coordinate
swap. The independent value contains the link and every challenge coordinate;
it is not a seed for another generator. All prior values remain unchanged. -/
def swap := MerklePrequery.swap (compile bindOnly before start writes) (opening bindOnly openingWrites)

theorem prefix_preserved (coins : (Point → Digest × C) × (Digest × C)) :
    (compile bindOnly before start writes).run
        (swap bindOnly before start writes openingWrites coins).1 =
      (compile bindOnly before start writes).run coins.1 :=
  MerklePrequery.prior_swap _ _ coins

theorem whole_answer (coins : (Point → Digest × C) × (Digest × C))
    (fresh : MerklePrequery.fresh (compile bindOnly before start writes) (opening bindOnly openingWrites) coins.1) :
    (swap bindOnly before start writes openingWrites coins).1
        (MerklePrequery.location (compile bindOnly before start writes) (opening bindOnly openingWrites) coins.1) =
      coins.2 := MerklePrequery.programmed_answer _ _ coins fresh

/-- The guarded refresh is an exact change of uniform oracle/answer coins,
including arbitrary subsequent oracle access. On a prior hit its answer is
retained; the concrete primary-mask counting theorem bounds that branch. -/
theorem refresh_sameDistribution [Fintype Point] [Fintype C]
    {Observed : Type} [DecidableEq Observed]
    (observe :
      (Finished (g := g) (fields := fields) (Advice := Advice) (Key := Key) (Base := Base)
        (C := C) (Request := Request) × List (Point × (Digest × C))) →
      (Digest × C) → (Point → Digest × C) → Observed) :
    LigeroFamily.SameDistribution
      (fun coins : (Point → Digest × C) × (Digest × C) =>
        observe ((compile bindOnly before start writes).run coins.1)
          (MerklePrequery.refreshedAnswer (compile bindOnly before start writes)
            (opening bindOnly openingWrites) coins)
          (swap bindOnly before start writes openingWrites coins).1)
      (fun coins : (Point → Digest × C) × (Digest × C) =>
        observe ((compile bindOnly before start writes).run coins.1)
          (coins.1 (MerklePrequery.location (compile bindOnly before start writes)
            (opening bindOnly openingWrites) coins.1)) coins.1) :=
  MerklePrequery.refresh_sameDistribution _ _ observe

end LfzkV2.Current.ZeroKnowledge.OracleRefresh
