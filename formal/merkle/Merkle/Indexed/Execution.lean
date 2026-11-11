import Merkle.Indexed.Commit
import Merkle.TreeCompose

/-! The indexed verifier as an actual oracle program. A descending heap
pass computes children before parents and queries only opened leaves and
internal path nodes. The operation at a vertex is shared by execution and
query accounting, so they cannot silently use different hash encodings. -/
namespace Merkle.Indexed
open RandomOracle

variable {Salt M D Enc : Type} [Inhabited D]
variable (codec : Codec Salt M D Enc)
variable (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)

/-- A static frontier/default value or one indexed hash input. -/
def operation (values : ℕ → D) (vertex : ℕ) : D ⊕ Enc :=
  if leaf : n ≤ vertex ∧ vertex < 2*n then
    if opened : (⟨vertex-n,by omega⟩ : Fin n) ∈ I then
      .inr (codec.leafEnc (proof.nonce ⟨_,opened⟩,a ⟨vertex-n,by omega⟩))
    else if frontier : vertex ∈ Heap.frontier n I then .inl (proof.frontierValue ⟨vertex,frontier⟩)
    else .inl default
  else if frontier : vertex ∈ Heap.frontier n I then .inl (proof.frontierValue ⟨vertex,frontier⟩)
  else if 0 < vertex ∧ vertex < n ∧ vertex ∈ Heap.pathSet n I then
    .inr (codec.nodeEnc vertex (values (2*vertex),values (2*vertex+1)))
  else .inl default

def execute (op : D ⊕ Enc) : Tree Enc D D 1 :=
  match op with
  | .inl value => .done value
  | .inr input => .query input fun value => .done value

omit [Inhabited D] in
theorem execute_value (op : D ⊕ Enc) (H : Enc → D) :
    ((execute op).run H).1 = Sum.elim id H op := by cases op <;> rfl

omit [Inhabited D] in
theorem execute_visible (op : D ⊕ Enc) (H : Enc → D) (input : Enc)
    (queried : op = .inr input) : (input,H input) ∈ ((execute op).run H).2 := by
  rw [queried]
  exact List.mem_cons_self

theorem operation_congr (H : Enc → D) (values : ℕ → D) (vertex : ℕ)
    (above : ∀ v, vertex < v → values v = checkValues (codec.withOracle H) n I a proof v) :
    operation codec n I a proof values vertex =
      operation codec n I a proof (checkValues (codec.withOracle H) n I a proof) vertex := by
  unfold operation
  split_ifs with leaf opened frontier frontier path
  all_goals try rfl
  rw [above (2*vertex) (by omega),above (2*vertex+1) (by omega)]

theorem operation_value (H : Enc → D) (vertex : ℕ) :
    Sum.elim id H (operation codec n I a proof (checkValues (codec.withOracle H) n I a proof) vertex) =
      checkValues (codec.withOracle H) n I a proof vertex := by
  conv_rhs => rw [checkValues]
  unfold operation
  split_ifs <;> rfl

def checkPass : (count : ℕ) → (ℕ → D) → Tree Enc D (ℕ → D) count
  | 0,values => .done values
  | count+1,values =>
      (execute (operation codec n I a proof values (count+1))).bind fun value =>
        checkPass count (Function.update values (count+1) value)

/-- The invariant and trace coverage are proved in one induction. The
initial array only needs correct values beyond the processed heap prefix. -/
theorem checkPass_run (H : Enc → D) : ∀ count values,
    (∀ v, count < v → values v = checkValues (codec.withOracle H) n I a proof v) →
    (∀ v, 0 < v → ((checkPass codec n I a proof count values).run H).1 v =
      checkValues (codec.withOracle H) n I a proof v) ∧
    (∀ vertex input, 0 < vertex → vertex ≤ count →
      operation codec n I a proof (checkValues (codec.withOracle H) n I a proof) vertex = .inr input →
      (input,H input) ∈ ((checkPass codec n I a proof count values).run H).2) := by
  intro count
  induction count with
  | zero =>
      intro values above
      exact ⟨fun v positive => above v positive,fun vertex _ positive bound _ => by omega⟩
  | succ count ih =>
      intro values above
      let op := operation codec n I a proof values (count+1)
      let value := ((execute op).run H).1
      have operationEq := operation_congr codec n I a proof H values (count+1) above
      have valueEq : value = checkValues (codec.withOracle H) n I a proof (count+1) := by
        dsimp only [value,op]
        rw [execute_value,operationEq,operation_value]
      have nextAbove : ∀ v, count < v → Function.update values (count+1) value v =
          checkValues (codec.withOracle H) n I a proof v := by
        intro v bound
        by_cases current : v = count+1
        · subst v
          rw [Function.update_self,valueEq]
        · rw [Function.update_of_ne current]
          exact above v (by omega)
      obtain ⟨correct,visible⟩ := ih (Function.update values (count+1) value) nextAbove
      rw [checkPass,Tree.run_bind]
      refine ⟨correct,?_⟩
      intro vertex input positive bound queried
      by_cases current : vertex = count+1
      · apply List.mem_append_left
        apply execute_visible
        exact operationEq.trans (current ▸ queried)
      · exact List.mem_append_right _ (visible vertex input positive (by omega) queried)

theorem checkValues_outside (H : Enc → D) (vertex : ℕ) (outside : 2*n ≤ vertex) :
    checkValues (codec.withOracle H) n I a proof vertex = default := by
  have frontier : vertex ∉ Heap.frontier n I := by
    intro member
    have bounds := Heap.mem_nodes.mp (Heap.mem_frontier_iff.mp member).2.1
    omega
  rw [checkValues]
  simp only [show ¬(n ≤ vertex ∧ vertex < 2*n) by omega,↓reduceDIte,frontier,
    show ¬(0 < vertex ∧ vertex < n ∧ vertex ∈ Heap.pathSet n I) by omega]

def check : Tree Enc D (ℕ → D) (2*n) := checkPass codec n I a proof (2*n) (fun _ => default)

theorem check_run (H : Enc → D) (vertex : ℕ) (positive : 0 < vertex) :
    ((check codec n I a proof).run H).1 vertex =
      checkValues (codec.withOracle H) n I a proof vertex := by
  exact (checkPass_run codec n I a proof H (2*n) (fun _ => default)
    (fun v above => (checkValues_outside codec n I a proof H v (by omega)).symm)).1 vertex positive

theorem check_visible (H : Enc → D) (vertex : ℕ) (input : Enc)
    (positive : 0 < vertex) (within : vertex < 2*n)
    (queried : operation codec n I a proof (checkValues (codec.withOracle H) n I a proof) vertex = .inr input) :
    (input,H input) ∈ ((check codec n I a proof).run H).2 := by
  exact (checkPass_run codec n I a proof H (2*n) (fun _ => default)
    (fun v above => (checkValues_outside codec n I a proof H v (by omega)).symm)).2
      vertex input positive (Nat.le_of_lt within) queried

/-- The mathematical check's hash inputs. This is also the support of the
executable check, without its query order or repeated entries. -/
noncomputable def checkTraceQueries (S : Scheme Salt M D Enc) (n : ℕ)
    (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D) : Finset Enc := by
  classical
  exact (Finset.Ico 1 (2*n)).biUnion fun vertex =>
    match operation S.toCodec n I a proof (checkValues S n I a proof) vertex with
    | .inl _ => ∅
    | .inr input => {input}

theorem mem_checkTraceQueries (S : Scheme Salt M D Enc) (n : ℕ)
    (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D) (input : Enc) :
    input ∈ checkTraceQueries S n I a proof ↔
      ∃ vertex, 0 < vertex ∧ vertex < 2*n ∧
        operation S.toCodec n I a proof (checkValues S n I a proof) vertex = .inr input := by
  classical
  unfold checkTraceQueries
  simp only [Finset.mem_biUnion,Finset.mem_Ico]
  constructor
  · rintro ⟨vertex,⟨positive,within⟩,member⟩
    refine ⟨vertex,positive,within,?_⟩
    split at member
    · simp at member
    · rename_i found hfound
      have same := Finset.mem_singleton.mp member
      exact same ▸ hfound
  · rintro ⟨vertex,positive,within,queried⟩
    refine ⟨vertex,⟨positive,within⟩,?_⟩
    rw [queried]
    exact Finset.mem_singleton_self _

end Merkle.Indexed
