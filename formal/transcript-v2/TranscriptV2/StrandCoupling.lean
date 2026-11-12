import TranscriptV2.FreshRenaming
import Mathlib.Algebra.BigOperators.Field

/-! Deferred sampling for digest-addressed challenge streams.

The raw adversary reads individual counter blocks. Sampling the rest of a
stream early changes neither those answers nor their joint distribution.
In particular a node may reserve its stream when its digest is obtained.
An already reserved stream is always reused, including after digest collisions.
This module does not condition on successful proofs or on a collision-free run.
-/
noncomputable section
namespace TranscriptV2.StrandCoupling
open Finset Merkle.RandomOracle
open scoped Classical

variable {P K D I Out : Type}
variable [DecidableEq P] [DecidableEq K] [DecidableEq I]

abbrev Stream (D I : Type) := I → D
abbrev Point (P K I : Type) := Sum P (K × I)

structure Cache (P K D I : Type) where
  nodes : P → Option D
  streams : K → Option (Stream D I)

def Cache.empty : Cache P K D I := ⟨fun _ => none,fun _ => none⟩

def Cache.node (state : Cache P K D I) (point : P) (digest : D) : Cache P K D I :=
  { state with nodes := Function.update state.nodes point (some digest) }

def Cache.stream (state : Cache P K D I) (digest : K) (bytes : Stream D I) : Cache P K D I :=
  { state with streams := Function.update state.streams digest (some bytes) }

private def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / Fintype.card A

private theorem average_congr {A : Type} [Fintype A] {f g : A → ℚ}
    (same : ∀ a, f a = g a) : average f = average g := by
  simp only [average]
  congr 1
  exact sum_congr rfl (fun a _ => same a)

private theorem average_equiv {A B : Type} [Fintype A] [Fintype B]
    (equiv : A ≃ B) (f : B → ℚ) : average (fun a => f (equiv a)) = average f := by
  unfold average
  rw [Fintype.card_congr equiv,Equiv.sum_comp equiv]

private theorem average_const {A : Type} [Fintype A] [Nonempty A] (value : ℚ) :
    average (fun _ : A => value) = value := by
  simp [average]

private theorem average_comm {A B : Type} [Fintype A] [Fintype B]
    (f : A → B → ℚ) :
    average (fun a => average (f a)) = average (fun b => average (fun a => f a b)) := by
  simp only [average,← sum_div,div_div]
  rw [sum_comm,mul_comm]

private theorem average_pair {A B : Type} [Fintype A] [Fintype B]
    (f : A × B → ℚ) : average f = average (fun a => average (fun b => f (a,b))) := by
  simp only [average,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← sum_div,div_div]
  rw [mul_comm]

private theorem average_left {A B : Type} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → ℚ) : average (fun a : A × B => f a.1) = average f := by
  rw [average_pair]
  exact average_congr (fun a => average_const (A := B) (f a))

private theorem average_right {A B : Type} [Fintype A] [Fintype B] [Nonempty A]
    (f : B → ℚ) : average (fun a : A × B => f a.2) = average f := by
  rw [average_pair]
  exact average_const (A := A) (average f)

omit [DecidableEq P] [DecidableEq I] in
private theorem stream_comm (state : Cache P K D I) (first second : K)
    (a b : Stream D I) (distinct : first ≠ second) :
    (state.stream first a).stream second b = (state.stream second b).stream first a := by
  simp only [Cache.stream]
  congr 1
  exact Function.update_comm distinct _ _ _

variable [Fintype D] [Nonempty D] [Fintype I]

/-- Exact lazy sampling of the two disjoint SHA domains. A stream's first
counter read samples its entire row; all later reads retain that same row. -/
def lazyMean (value : Out → ℚ) : {fuel : ℕ} →
    Tree (Point P K I) D Out fuel → Cache P K D I → ℚ
  | _, .done output, _ => value output
  | _, .query (.inl point) next, state =>
      match state.nodes point with
      | some digest => lazyMean value (next digest) state
      | none => average fun digest => lazyMean value (next digest) (state.node point digest)
  | _, .query (.inr (digest,counter)) next, state =>
      match state.streams digest with
      | some bytes => lazyMean value (next (bytes counter)) state
      | none => average fun bytes => lazyMean value (next (bytes counter)) (state.stream digest bytes)

/-- An unobserved row can be sampled now, even if the adaptive program may
never read it. This equality retains every rejected and unused counter block. -/
theorem read_ahead (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) (state : Cache P K D I) (digest : K)
    (fresh : state.streams digest = none) :
    lazyMean value program state =
      average (fun bytes => lazyMean value program (state.stream digest bytes)) := by
  induction program generalizing state with
  | done output =>
      simpa only [lazyMean] using (average_const (A := Stream D I) (value output)).symm
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some answer =>
              simpa only [lazyMean,known,Cache.stream] using ih answer state fresh
          | none =>
              simp only [lazyMean,known,Cache.stream]
              calc
                _ = average (fun answer => average (fun bytes =>
                    lazyMean value (next answer) ((state.node point answer).stream digest bytes))) := by
                  apply average_congr
                  intro answer
                  exact ih answer (state.node point answer) fresh
                _ = _ := average_comm _
      | inr address =>
          rcases address with ⟨parent,counter⟩
          by_cases same : parent = digest
          · subst parent
            simp only [lazyMean,fresh,Cache.stream,Function.update_self]
          · cases known : state.streams parent with
            | some bytes =>
                simpa only [lazyMean,known,Cache.stream,Function.update_of_ne same] using
                  ih (bytes counter) state fresh
            | none =>
                simp only [lazyMean,known,Cache.stream,Function.update_of_ne same]
                calc
                  _ = average (fun bytes => average (fun later =>
                      lazyMean value (next (bytes counter)) ((state.stream parent bytes).stream digest later))) := by
                    apply average_congr
                    intro bytes
                    apply ih (bytes counter) (state.stream parent bytes)
                    simpa only [Cache.stream,Function.update_of_ne (Ne.symm same)] using fresh
                  _ = average (fun later => average (fun bytes =>
                      lazyMean value (next (bytes counter)) ((state.stream parent bytes).stream digest later))) :=
                    average_comm _
                  _ = _ := by
                    apply average_congr
                    intro later
                    apply average_congr
                    intro bytes
                    rw [stream_comm state parent digest bytes later same]
                    rfl

/- A node's stream address may contain public position information in addition
to its digest. Its key space is independent of the hash output space. No
injectivity premise is needed: repeated keys retain their already sampled row. -/
variable (streamKey : P → D → K)

/-- Reserve a fresh node's stream immediately. A previously observed row
is retained verbatim, rather than replaced by a new independent challenge. -/
def eagerMean (streamKey : P → D → K) (value : Out → ℚ) : {fuel : ℕ} →
    Tree (Point P K I) D Out fuel → Cache P K D I → ℚ
  | _, .done output, _ => value output
  | _, .query (.inl point) next, state =>
      match state.nodes point with
      | some digest => eagerMean streamKey value (next digest) state
      | none => average fun digest =>
          match state.streams (streamKey point digest) with
          | some _ => eagerMean streamKey value (next digest) (state.node point digest)
          | none => average fun bytes =>
              eagerMean streamKey value (next digest) ((state.node point digest).stream (streamKey point digest) bytes)
  | _, .query (.inr (digest,counter)) next, state =>
      match state.streams digest with
      | some bytes => eagerMean streamKey value (next (bytes counter)) state
      | none => average fun bytes => eagerMean streamKey value (next (bytes counter)) (state.stream digest bytes)

/-- Early stream allocation preserves the distribution of every output of
an arbitrary adaptive raw-query program. No query-order or collision premise
is required; equality holds because existing rows are never overwritten. -/
theorem eager_eq_lazy (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) (state : Cache P K D I) :
    eagerMean streamKey value program state = lazyMean value program state := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest => simpa only [eagerMean,lazyMean,known] using ih digest state
          | none =>
              simp only [eagerMean,lazyMean,known]
              apply average_congr
              intro digest
              cases row : state.streams (streamKey point digest) with
              | some bytes => simpa only [row] using ih digest (state.node point digest)
              | none =>
                  calc
                    _ = average (fun bytes => lazyMean value (next digest)
                        ((state.node point digest).stream (streamKey point digest) bytes)) :=
                      average_congr (fun bytes => ih digest _)
                    _ = _ := (read_ahead value (next digest) (state.node point digest) (streamKey point digest) row).symm
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes => simpa only [eagerMean,lazyMean,known] using ih (bytes counter) state
          | none =>
              simp only [eagerMean,lazyMean,known]
              exact average_congr (fun bytes => ih (bytes counter) _)

/-! The sampling laws above are connected to uniform oracle tables through
fresh query programs. Both programs use one independent `(digest, stream)`
answer per newly sampled coordinate; unused coordinates carry no information
to the raw adversary. Eager sampling reuses the otherwise unused stream at
a node coordinate, rather than assuming another independent random oracle. -/

abbrev SamplePoint (P K : Type) := Sum P K
abbrev Sample (D I : Type) := D × Stream D I

def Cache.known (state : Cache P K D I) : SamplePoint P K → Prop
  | .inl point => (state.nodes point).isSome
  | .inr digest => (state.streams digest).isSome

def lazyTree : {fuel : ℕ} → Tree (Point P K I) D Out fuel → Cache P K D I →
    Tree (SamplePoint P K) (Sample D I) Out fuel
  | _, .done output, _ => .done output
  | _, .query (.inl point) next, state =>
      match state.nodes point with
      | some digest => (lazyTree (next digest) state).weaken
      | none => .query (.inl point) fun answer =>
          lazyTree (next answer.1) (state.node point answer.1)
  | _, .query (.inr (digest,counter)) next, state =>
      match state.streams digest with
      | some bytes => (lazyTree (next (bytes counter)) state).weaken
      | none => .query (.inr digest) fun answer =>
          lazyTree (next (answer.2 counter)) (state.stream digest answer.2)

def eagerTree (streamKey : P → D → K) : {fuel : ℕ} → Tree (Point P K I) D Out fuel → Cache P K D I →
    Tree (SamplePoint P K) (Sample D I) Out fuel
  | _, .done output, _ => .done output
  | _, .query (.inl point) next, state =>
      match state.nodes point with
      | some digest => (eagerTree streamKey (next digest) state).weaken
      | none => .query (.inl point) fun answer =>
          let updated := state.node point answer.1
          let reserved := match state.streams (streamKey point answer.1) with
            | some _ => updated
            | none => updated.stream (streamKey point answer.1) answer.2
          eagerTree streamKey (next answer.1) reserved
  | _, .query (.inr (digest,counter)) next, state =>
      match state.streams digest with
      | some bytes => (eagerTree streamKey (next (bytes counter)) state).weaken
      | none => .query (.inr digest) fun answer =>
          eagerTree streamKey (next (answer.2 counter)) (state.stream digest answer.2)

omit [DecidableEq K] [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
private theorem known_node (state : Cache P K D I) (point : P) (digest : D)
    (key : SamplePoint P K) (known : key = .inl point ∨ state.known key) :
    (state.node point digest).known key := by
  cases key with
  | inl other =>
      by_cases same : other = point <;> simp_all [Cache.known,Cache.node]
  | inr other => simpa only [Cache.known,Cache.node,Sum.inr_ne_inl,false_or] using known

omit [DecidableEq P] [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
private theorem known_stream (state : Cache P K D I) (digest : K) (bytes : Stream D I)
    (key : SamplePoint P K) (known : key = .inr digest ∨ state.known key) :
    (state.stream digest bytes).known key := by
  cases key with
  | inl other => simpa only [Cache.known,Cache.stream,Sum.inl_ne_inr,false_or] using known
  | inr other =>
      by_cases same : other = digest <;> simp_all [Cache.known,Cache.stream]

omit [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
theorem lazyTree_fresh {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) : FreshOracle.FreshFrom state.known (lazyTree program state) := by
  induction program generalizing state with
  | done output => trivial
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest => simpa only [lazyTree,known] using (ih digest state).weaken
          | none =>
              simp only [lazyTree,known,FreshOracle.FreshFrom]
              refine ⟨by simp [Cache.known,known],?_⟩
              intro answer
              exact (ih answer.1 (state.node point answer.1)).mono
                (fun key old => known_node state point answer.1 key old)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes => simpa only [lazyTree,known] using (ih (bytes counter) state).weaken
          | none =>
              simp only [lazyTree,known,FreshOracle.FreshFrom]
              refine ⟨by simp [Cache.known,known],?_⟩
              intro answer
              exact (ih (answer.2 counter) (state.stream digest answer.2)).mono
                (fun key old => known_stream state digest answer.2 key old)

omit [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
theorem eagerTree_fresh {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) : FreshOracle.FreshFrom state.known (eagerTree streamKey program state) := by
  induction program generalizing state with
  | done output => trivial
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest => simpa only [eagerTree,known] using (ih digest state).weaken
          | none =>
              simp only [eagerTree,known,FreshOracle.FreshFrom]
              refine ⟨by simp [Cache.known,known],?_⟩
              intro answer
              cases row : state.streams (streamKey point answer.1) with
              | some bytes =>
                  exact (ih answer.1 (state.node point answer.1)).mono
                    (fun key old => known_node state point answer.1 key old)
              | none =>
                  exact (ih answer.1 ((state.node point answer.1).stream (streamKey point answer.1) answer.2)).mono
                    (fun key old => known_stream (state.node point answer.1) (streamKey point answer.1) answer.2 key
                      (Or.inr (known_node state point answer.1 key old)))
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes => simpa only [eagerTree,known] using (ih (bytes counter) state).weaken
          | none =>
              simp only [eagerTree,known,FreshOracle.FreshFrom]
              refine ⟨by simp [Cache.known,known],?_⟩
              intro answer
              exact (ih (answer.2 counter) (state.stream digest answer.2)).mono
                (fun key old => known_stream state digest answer.2 key old)

theorem lazyTree_mean (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) (state : Cache P K D I) :
    FreshOracle.mean value (lazyTree program state) = lazyMean value program state := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest => simpa only [lazyTree,lazyMean,known,FreshOracle.mean_weaken] using ih digest state
          | none =>
              simp only [lazyTree,lazyMean,known,FreshOracle.mean]
              change average (fun answer : Sample D I =>
                FreshOracle.mean value (lazyTree (next answer.1) (state.node point answer.1))) = _
              simp_rw [ih]
              simpa only [lazyMean,known] using average_left (B := Stream D I)
                (fun digest => lazyMean value (next digest) (state.node point digest))
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes => simpa only [lazyTree,lazyMean,known,FreshOracle.mean_weaken] using ih (bytes counter) state
          | none =>
              simp only [lazyTree,lazyMean,known,FreshOracle.mean]
              change average (fun answer : Sample D I =>
                FreshOracle.mean value (lazyTree (next (answer.2 counter)) (state.stream digest answer.2))) = _
              simp_rw [ih]
              simpa only [lazyMean,known] using average_right (A := D)
                (fun bytes => lazyMean value (next (bytes counter)) (state.stream digest bytes))

theorem eagerTree_mean (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) (state : Cache P K D I) :
    FreshOracle.mean value (eagerTree streamKey program state) = eagerMean streamKey value program state := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest => simpa only [eagerTree,eagerMean,known,FreshOracle.mean_weaken] using ih digest state
          | none =>
              simp only [eagerTree,eagerMean,known,FreshOracle.mean]
              change average (A := Sample D I) _ = _
              rw [average_pair]
              apply average_congr
              intro digest
              cases row : state.streams (streamKey point digest) with
              | some bytes =>
                  simp only [row,ih]
                  exact average_const (A := Stream D I) _
              | none =>
                  simp only [row]
                  exact average_congr (fun bytes => ih digest _)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes => simpa only [eagerTree,eagerMean,known,FreshOracle.mean_weaken] using ih (bytes counter) state
          | none =>
              simp only [eagerTree,eagerMean,known,FreshOracle.mean]
              change average (fun answer : Sample D I =>
                FreshOracle.mean value (eagerTree streamKey (next (answer.2 counter)) (state.stream digest answer.2))) = _
              simp_rw [ih]
              simpa only [eagerMean,known] using average_right (A := D)
                (fun bytes => eagerMean streamKey value (next (bytes counter)) (state.stream digest bytes))

/-- The two active coordinates are precisely the node hash and the indexed
PRF stream. Other coordinates are unused independent padding in the sample
space, not extra answers revealed to the adversary. -/
def rawOracle (H : SamplePoint P K → Sample D I) : Point P K I → D
  | .inl point => (H (.inl point)).1
  | .inr (digest,counter) => (H (.inr digest)).2 counter

omit [DecidableEq P] [DecidableEq K] [Fintype D] [Nonempty D] [Fintype I] in
/-- Split the padded sample table into the actual raw oracle and unused
independent coordinates. Every raw SHA input has exactly one active entry. -/
def rawTableEquiv : (SamplePoint P K → Sample D I) ≃
    ((Point P K I → D) × ((P → Stream D I) × (K → D))) where
  toFun H := (rawOracle H,(fun point => (H (.inl point)).2,fun digest => (H (.inr digest)).1))
  invFun table
    | .inl point => (table.1 (.inl point),table.2.1 point)
    | .inr digest => (table.2.2 digest,fun counter => table.1 (.inr (digest,counter)))
  left_inv H := by funext point; cases point <;> rfl
  right_inv table := by
    rcases table with ⟨oracle,rows,digests⟩
    apply Prod.ext
    · funext point
      cases point <;> rfl
    · rfl

theorem rawOracle_uniform [Fintype P] [Fintype K] (value : (Point P K I → D) → ℚ) :
    (∑ H : SamplePoint P K → Sample D I, value (rawOracle H)) /
        (Fintype.card (Sample D I) : ℚ)^Fintype.card (SamplePoint P K) =
      (∑ H : Point P K I → D, value H) /
        (Fintype.card D : ℚ)^Fintype.card (Point P K I) := by
  have same : average (fun H : SamplePoint P K → Sample D I => value (rawOracle H)) =
      average value := by
    exact (average_equiv rawTableEquiv (fun table => value table.1)).trans (average_left value)
  simpa only [average,Fintype.card_fun,Nat.cast_pow] using same

def Cache.Agrees (state : Cache P K D I) (H : SamplePoint P K → Sample D I) : Prop :=
  (∀ point digest, state.nodes point = some digest → digest = (H (.inl point)).1) ∧
  (∀ digest bytes, state.streams digest = some bytes → bytes = (H (.inr digest)).2)

omit [DecidableEq K] [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
private theorem agrees_node (state : Cache P K D I) (H : SamplePoint P K → Sample D I)
    (agree : state.Agrees H) (point : P) :
    (state.node point (H (.inl point)).1).Agrees H := by
  refine ⟨?_,agree.2⟩
  intro other digest found
  by_cases same : other = point
  · subst other
    simpa only [Cache.node,Function.update_self,Option.some.injEq] using found.symm
  · exact agree.1 other digest (by simpa only [Cache.node,Function.update_of_ne same] using found)

omit [DecidableEq P] [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
private theorem agrees_stream (state : Cache P K D I) (H : SamplePoint P K → Sample D I)
    (agree : state.Agrees H) (digest : K) :
    (state.stream digest (H (.inr digest)).2).Agrees H := by
  refine ⟨agree.1,?_⟩
  intro other bytes found
  by_cases same : other = digest
  · subst other
    simpa only [Cache.stream,Function.update_self,Option.some.injEq] using found.symm
  · exact agree.2 other bytes (by simpa only [Cache.stream,Function.update_of_ne same] using found)

omit [DecidableEq I] [Fintype D] [Nonempty D] [Fintype I] in
theorem lazyTree_run {fuel : ℕ} (program : Tree (Point P K I) D Out fuel)
    (state : Cache P K D I) (H : SamplePoint P K → Sample D I) (agree : state.Agrees H) :
    ((lazyTree program state).run H).1 = (program.run (rawOracle H)).1 := by
  induction program generalizing state with
  | done output => rfl
  | query point next ih =>
      cases point with
      | inl point =>
          cases known : state.nodes point with
          | some digest =>
              have answer := agree.1 point digest known
              simpa only [lazyTree,known,Tree.run_weaken,Tree.run_query,rawOracle,answer] using
                ih (H (.inl point)).1 state agree
          | none =>
              simpa only [lazyTree,known,Tree.run_query,rawOracle] using
                ih (H (.inl point)).1 _ (agrees_node state H agree point)
      | inr address =>
          rcases address with ⟨digest,counter⟩
          cases known : state.streams digest with
          | some bytes =>
              have answer := agree.2 digest bytes known
              simpa only [lazyTree,known,Tree.run_weaken,Tree.run_query,rawOracle,answer] using
                ih ((H (.inr digest)).2 counter) state agree
          | none =>
              simpa only [lazyTree,known,Tree.run_query,rawOracle] using
                ih ((H (.inr digest)).2 counter) _ (agrees_stream state H agree digest)

/-- Equality of output laws for the actual indexed-block interface and the
eager node/stream simulation. The source may itself record all its answers,
run a verifier, or execute an observer before and after producing its proof. -/
theorem eager_uniform [Fintype P] [Fintype K] (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) :
    (∑ H : SamplePoint P K → Sample D I,
      value (((eagerTree streamKey program Cache.empty).run H).1)) /
        (Fintype.card (Sample D I) : ℚ)^Fintype.card (SamplePoint P K) =
    (∑ H : SamplePoint P K → Sample D I, value (program.run (rawOracle H)).1) /
        (Fintype.card (Sample D I) : ℚ)^Fintype.card (SamplePoint P K) := by
  rw [FreshOracle.uniform_mean value _ (eagerTree_fresh streamKey program Cache.empty),
    eagerTree_mean,eager_eq_lazy,← lazyTree_mean,
    ← FreshOracle.uniform_mean value _ (lazyTree_fresh program Cache.empty)]
  congr 1
  apply sum_congr rfl
  intro H _
  rw [lazyTree_run program Cache.empty H (by simp [Cache.Agrees,Cache.empty])]

/-- Direct comparison with one uniform raw oracle, rather than a separate
oracle assumption about digest-indexed streams. Both domains are ordinary
inputs of the same random function. -/
theorem eager_raw_uniform [Fintype P] [Fintype K] (value : Out → ℚ) {fuel : ℕ}
    (program : Tree (Point P K I) D Out fuel) :
    (∑ H : SamplePoint P K → Sample D I,
      value (((eagerTree streamKey program Cache.empty).run H).1)) /
        (Fintype.card (Sample D I) : ℚ)^Fintype.card (SamplePoint P K) =
      (∑ H : Point P K I → D, value ((program.run H).1)) /
        (Fintype.card D : ℚ)^Fintype.card (Point P K I) := by
  rw [eager_uniform]
  exact rawOracle_uniform (fun H => value ((program.run H).1))

end TranscriptV2.StrandCoupling
