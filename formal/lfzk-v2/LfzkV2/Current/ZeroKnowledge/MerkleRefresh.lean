import LfzkV2.Current.ZeroKnowledge.MerklePrequery

/-! Iterating fresh-coordinate refresh along an honest causal computation.
At each step the input is computed by replaying only the already completed
history, including an arbitrary earlier observer.  Its new answer coin has
not been used by that history.  Later swaps preserve every earlier answer.

The equivalence is total even on repeated inputs, where the original answer
is retained.  The separate freshness analysis identifies when the resulting
labels are all the independently sampled coins. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleRefresh

open Merkle.RandomOracle MerklePrequery
open scoped Classical

variable {Query Answer State : Type} {fuel total : ℕ}

/-- Separate one new answer coin from the rest without discarding any coins. -/
def splitCoin (i : Fin total) :
    ((Query → Answer) × (Fin total → Answer)) ≃
      (((Query → Answer) × Answer) × ({j : Fin total // j ≠ i} → Answer)) :=
  (Equiv.prodCongr (Equiv.refl _) (Equiv.funSplitAt i Answer)).trans
    (Equiv.prodAssoc _ _ _).symm

def stepEquiv (before : Tree Query Answer State fuel) (input : State → Query)
    (i : Fin total) :
    ((Query → Answer) × (Fin total → Answer)) ≃
      ((Query → Answer) × (Fin total → Answer)) :=
  (splitCoin i).trans
    (((swapEquiv before input).prodCongr (Equiv.refl _)).trans (splitCoin i).symm)

@[simp] theorem step_oracle (before : Tree Query Answer State fuel) (input : State → Query)
    (i : Fin total) (coins : (Query → Answer) × (Fin total → Answer)) :
    (stepEquiv before input i coins).1 = (swap before input (coins.1,coins.2 i)).1 := rfl

theorem step_tape_other (before : Tree Query Answer State fuel) (input : State → Query)
    (i j : Fin total) (different : j ≠ i)
    (coins : (Query → Answer) × (Fin total → Answer)) :
    (stepEquiv before input i coins).2 j = coins.2 j := by
  simp [stepEquiv,splitCoin,Equiv.funSplitAt,Equiv.piSplitAt,different]

variable (before : Tree Query Answer State fuel)
variable (input : ℕ → State → Query) (update : ℕ → State → Answer → State)

/-- Append exactly one honest query, keeping the fuel arithmetic definitional. -/
def append : {bound : ℕ} → Tree Query Answer State bound →
    (State → Query) → (State → Answer → State) → Tree Query Answer State (bound+1)
  | _,.done state,query,next => .query (query state) fun answer => .done (next state answer)
  | _,.query query next,queryOf,updateState =>
      .query query fun answer => append (next answer) queryOf updateState

theorem append_run {bound : ℕ} (body : Tree Query Answer State bound)
    (query : State → Query) (next : State → Answer → State) (H : Query → Answer) :
    (append body query next).run H =
      (next (body.run H).1 (H (query (body.run H).1)),
        (body.run H).2 ++ [(query (body.run H).1,H (query (body.run H).1))]) := by
  induction body with
  | done state => rfl
  | query q continuation ih => simp only [append,Tree.run_query,ih,List.cons_append]

/-- Replaying the first `count` honest queries has no access to later
answer coins.  This definition also records the observer's original trace. -/
def history (before : Tree Query Answer State fuel)
    (input : ℕ → State → Query) (update : ℕ → State → Answer → State) :
    (count : ℕ) → Tree Query Answer State (fuel+count)
  | 0 => before
  | count+1 => append (history before input update count) (input count) (update count)

theorem history_next (count : ℕ) (H : Query → Answer) :
    (history before input update (count+1)).run H =
      (update count ((history before input update count).run H).1
        (H (input count ((history before input update count).run H).1)),
       ((history before input update count).run H).2 ++
        [(input count ((history before input update count).run H).1,
          H (input count ((history before input update count).run H).1))]) := by
  exact append_run _ _ _ _

theorem prior_trace (count : ℕ) (H : Query → Answer) :
    (before.run H).2 <+: ((history before input update count).run H).2 := by
  induction count with
  | zero => exact List.prefix_refl _
  | succ count ih =>
      rw [history_next]
      exact ih.trans (List.prefix_append _ _)

def refresh (before : Tree Query Answer State fuel)
    (input : ℕ → State → Query) (update : ℕ → State → Answer → State) :
    (count : ℕ) → count ≤ total →
    ((Query → Answer) × (Fin total → Answer)) ≃
      ((Query → Answer) × (Fin total → Answer))
  | 0, _ => Equiv.refl _
  | count+1, fits =>
      (refresh before input update count (by omega)).trans
        (stepEquiv (history before input update count) (input count) ⟨count,by omega⟩)

theorem prior_step (count : ℕ) (i : Fin total)
    (coins : (Query → Answer) × (Fin total → Answer)) :
    before.run (stepEquiv (history before input update count) (input count) i coins).1 =
      before.run coins.1 := by
  apply Tree.run_congr_on_trace
  intro qa member
  have prefixMember := (prior_trace before input update count coins.1).subset member
  have preserved := prior_swap (history before input update count) (input count)
    (coins.1,coins.2 i)
  rw [← preserved] at prefixMember
  exact (Tree.trace_sound _ _ qa prefixMember).symm

theorem prior_refresh (count : ℕ) (fits : count ≤ total)
    (coins : (Query → Answer) × (Fin total → Answer)) :
    before.run (refresh before input update count fits coins).1 = before.run coins.1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change before.run
        (stepEquiv (history before input update count) (input count) _
          (refresh before input update count _ coins)).1 = _
      rw [prior_step,ih]

theorem future_coin (count : ℕ) (fits : count ≤ total) (j : Fin total)
    (unused : count ≤ j.val) (coins : (Query → Answer) × (Fin total → Answer)) :
    (refresh before input update count fits coins).2 j = coins.2 j := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (stepEquiv (history before input update count) (input count) ⟨count,_⟩
        (refresh before input update count _ coins)).2 j = _
      rw [step_tape_other _ _ _ j (by
        intro same
        have value : j.val = count := congrArg Fin.val same
        omega)]
      exact ih (by omega) (by omega)

/-- Execute the same state updates using an independent answer for every
step. This is an analysis experiment; the real protocol still queries its
oracle at the causal input determined by the current state. -/
def sampled (update : ℕ → State → Answer → State) (initial : State)
    (tape : Fin total → Answer) : (count : ℕ) → count ≤ total → State
  | 0,_ => initial
  | count+1,fits => update count (sampled update initial tape count (by omega))
      (tape ⟨count,by omega⟩)

/-- Independent-label execution, retaining all earlier answers in its view. -/
def sampledRun (input : ℕ → State → Query) (update : ℕ → State → Answer → State)
    (initial : State × List (Query × Answer)) (tape : Fin total → Answer) :
    (count : ℕ) → count ≤ total → State × List (Query × Answer)
  | 0,_ => initial
  | count+1,fits =>
      let earlier := sampledRun input update initial tape count (by omega)
      let answer := tape ⟨count,by omega⟩
      (update count earlier.1 answer,earlier.2++[(input count earlier.1,answer)])

theorem sampledRun_state (initial : State × List (Query × Answer))
    (tape : Fin total → Answer) (count : ℕ) (fits : count ≤ total) :
    (sampledRun input update initial tape count fits).1 =
      sampled update initial.1 tape count fits := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [sampledRun,sampled,ih]

/-- Only freshness of the already processed steps is used. In particular,
this lemma can establish freshness inductively rather than assume all future
queries are fresh in advance. -/
theorem sampled_run (coins : (Query → Answer) × (Fin total → Answer))
    (count : ℕ) (fits : count ≤ total)
    (unused : ∀ i : Fin count,
      fresh (history before input update i.val) (input i.val)
        (refresh before input update i.val (by omega) coins).1) :
    (history before input update count).run (refresh before input update count fits coins).1 =
      sampledRun input update (before.run coins.1) coins.2 count fits := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let bound : count ≤ total := by omega
      let i : Fin total := ⟨count,by omega⟩
      let mid := refresh before input update count bound coins
      let next := stepEquiv (history before input update count) (input count) i mid
      have preserved : (history before input update count).run next.1 =
          (history before input update count).run mid.1 :=
        prior_swap (history before input update count) (input count) (mid.1,mid.2 i)
      have answer : next.1 (input count ((history before input update count).run mid.1).1) =
          mid.2 i := programmed_answer _ _ (mid.1,mid.2 i) (unused ⟨count,by omega⟩)
      have previous : (history before input update count).run mid.1 =
          sampledRun input update (before.run coins.1) coins.2 count bound :=
        ih bound (fun j => unused ⟨j.val,by have := j.isLt; omega⟩)
      have future : mid.2 i = coins.2 i := future_coin before input update count bound i
        (Nat.le_refl _) coins
      change (history before input update (count+1)).run next.1 = _
      rw [history_next,preserved,answer,future,previous]
      rfl

/-- The independently sampled experiment identifies its own bad event:
the next input has already appeared in its prior trace. Off that event, the
causal refresh really uses every independent label. This removes any need
for a supplied freshness certificate about the refreshed oracle. -/
theorem fresh_of_sampled (coins : (Query → Answer) × (Fin total → Answer))
    (good : ∀ i : Fin total, ∀ qa ∈
      (sampledRun input update (before.run coins.1) coins.2 i.val (Nat.le_of_lt i.isLt)).2,
      qa.1 ≠ input i.val
        (sampledRun input update (before.run coins.1) coins.2 i.val (Nat.le_of_lt i.isLt)).1) :
    ∀ i : Fin total,
      fresh (history before input update i.val) (input i.val)
        (refresh before input update i.val (Nat.le_of_lt i.isLt) coins).1 := by
  intro i
  have all : ∀ count, (fits : count ≤ total) → ∀ j : Fin count,
      fresh (history before input update j.val) (input j.val)
        (refresh before input update j.val (by omega) coins).1 := by
    intro count
    induction count with
    | zero => intro _ j; exact Fin.elim0 j
    | succ count ih =>
        intro fits j
        have bound : count ≤ total := by omega
        by_cases earlier : j.val < count
        · exact ih bound ⟨j.val,earlier⟩
        · have last : j.val = count := by have := j.isLt; omega
          have lastFin : j = Fin.last count := Fin.ext last
          subst j
          have replay := sampled_run before input update coins count bound (ih bound)
          unfold fresh location
          change ∀ qa ∈ ((history before input update count).run
            (refresh before input update count bound coins).1).2,
            qa.1 ≠ input count ((history before input update count).run
              (refresh before input update count bound coins).1).1
          rw [replay]
          exact good ⟨count,by omega⟩
  exact all total (le_refl _) i

/-- On fresh steps the honest oracle computation after the bijection has
exactly the independent labels.  This identifies the experiment; bounding
the complement is a separate commitment-input and prior-hit calculation. -/
theorem sampled_history (coins : (Query → Answer) × (Fin total → Answer))
    (unused : ∀ i : Fin total,
      fresh (history before input update i.val) (input i.val)
        (refresh before input update i.val (Nat.le_of_lt i.isLt) coins).1)
    (count : ℕ) (fits : count ≤ total) :
    ((history before input update count).run
      (refresh before input update count fits coins).1).1 =
      sampled update (before.run coins.1).1 coins.2 count fits := by
  have replay := sampled_run before input update coins count fits
    (fun i => unused ⟨i.val,by have := i.isLt; omega⟩)
  exact (congrArg Prod.fst replay).trans
    (sampledRun_state input update (before.run coins.1) coins.2 count fits)

theorem refresh_outside (coins : (Query → Answer) × (Fin total → Answer))
    (unused : ∀ i : Fin total,
      fresh (history before input update i.val) (input i.val)
        (refresh before input update i.val (Nat.le_of_lt i.isLt) coins).1)
    (query : Query)
    (outside : ∀ i : Fin total,
      query ≠ input i.val (sampled update (before.run coins.1).1 coins.2 i.val
        (Nat.le_of_lt i.isLt)))
    (count : ℕ) (fits : count ≤ total) :
    (refresh before input update count fits coins).1 query = coins.1 query := by
  induction count with
  | zero => rfl
  | succ count ih =>
      let bound : count ≤ total := by omega
      let i : Fin total := ⟨count,by omega⟩
      let mid := refresh before input update count bound coins
      have different : query ≠ location (history before input update count) (input count) mid.1 := by
        change query ≠ input count ((history before input update count).run mid.1).1
        rw [sampled_history before input update coins unused count bound]
        exact outside i
      change (swap (history before input update count) (input count) (mid.1,mid.2 i)).1 query = _
      have unusedNow : fresh (history before input update count) (input count) mid.1 := unused i
      simp only [swap,if_pos unusedNow]
      rw [Function.update_of_ne different]
      exact ih bound

/-- All subsequent computation may inspect the entire resulting oracle.
No new statistical error is introduced by the causal refresh operation. -/
theorem refresh_sameDistribution [DecidableEq Query] [Fintype Query] [Fintype Answer]
    {View : Type} [DecidableEq View]
    (count : ℕ) (fits : count ≤ total)
    (observe : ((Query → Answer) × (Fin total → Answer)) → View) :
    LigeroFamily.SameDistribution
      (fun coins => observe (refresh before input update count fits coins)) observe := by
  apply LigeroFamily.sameDistribution_of_equiv (refresh before input update count fits)
  intro coins
  rfl

end LfzkV2.Current.ZeroKnowledge.MerkleRefresh
