import Mathlib

/-!
# The binary-heap tree

Models the tree layout of `rust/runtime/merkle/src/heap.rs`: a 1-indexed array
of size `2n`; the root is at position `1`, the leaves at positions `n..2n-1`,
and node `v < n` has children `2v` and `2v+1`. The layout is defined for every
`n ≥ 1` (no power-of-two assumption); `SPEC.md` §2 collects the mathematics.

Everything here is pure combinatorics (no hashing): paths, copaths, the
frontier `F(I) = copath(I) \ path(I)` (`SPEC` Def. 2.3), the frontier
partition of the unopened leaves (`SPEC` Lemma 2.4), and frontier
independence (`SPEC` Lemma 2.5 = notes Claim 18.6.7).
-/

open Finset Nat

set_option autoImplicit true

namespace Heap

/-! ## Nodes, leaves, internal nodes -/

/-- Heap positions `1 .. 2n-1` (position `0` is unused). -/
def nodes (n : ℕ) : Finset ℕ := Icc 1 (2 * n - 1)

/-- Leaf positions `n .. 2n-1`; leaf index `i : Fin n` sits at position `n + i`. -/
def leaves (n : ℕ) : Finset ℕ := Icc n (2 * n - 1)

/-- Internal positions `1 .. n-1`. -/
def internals (n : ℕ) : Finset ℕ := Icc 1 (n - 1)

lemma mem_nodes {n v : ℕ} : v ∈ nodes n ↔ 1 ≤ v ∧ v ≤ 2 * n - 1 := by
  simp [nodes]

lemma mem_leaves {n v : ℕ} : v ∈ leaves n ↔ n ≤ v ∧ v ≤ 2 * n - 1 := by
  simp [leaves]

lemma mem_internals {n v : ℕ} : v ∈ internals n ↔ 1 ≤ v ∧ v ≤ n - 1 := by
  simp [internals]

lemma nodes_decomp (n : ℕ) (hn : 0 < n) : nodes n = internals n ∪ leaves n := by
  ext v; simp [mem_nodes, mem_internals, mem_leaves]; omega

lemma internals_disjoint_leaves (n : ℕ) : Disjoint (internals n) (leaves n) := by
  rw [Finset.disjoint_left]; intro v hv hi
  simp [mem_internals, mem_leaves] at hv hi; omega

lemma leaf_pos_mem_leaves (n : ℕ) (i : Fin n) : n + i.val ∈ leaves n := by
  simp [mem_leaves]; omega

lemma leaf_pos_inj {n : ℕ} {i j : Fin n} (h : n + i.val = n + j.val) : i = j := by
  ext; omega

lemma pos_of_mem_nodes {n v : ℕ} (hv : v ∈ nodes n) : 0 < v := by
  simp [mem_nodes] at hv; omega

/-! ## Children, parent, sibling -/

def leftChild (v : ℕ) : ℕ := 2 * v

def rightChild (v : ℕ) : ℕ := 2 * v + 1

def parent (v : ℕ) : ℕ := v / 2

/-- The sibling of a node. For `v > 1` this is the other child of `parent v`. -/
def sibling (v : ℕ) : ℕ := if v % 2 = 0 then v + 1 else v - 1

/-- Maximum depth of any node of `T_n` (`⌈log₂ n⌉` for `n ≥ 2`). -/
def heapDepth (n : ℕ) : ℕ := Nat.log2 (2 * n - 1)

lemma child_lt_of_internal {n v : ℕ} (hv : v < n) : 2 * v + 1 < 2 * n := by omega

lemma parent_lt (v : ℕ) (hv : 2 ≤ v) : v / 2 < v := by omega

lemma sibling_of_even (v : ℕ) (h : v % 2 = 0) : sibling v = v + 1 := by simp [sibling, h]

lemma sibling_of_odd (v : ℕ) (h : v % 2 = 1) : sibling v = v - 1 := by simp [sibling, h]

lemma div2_of_even (v : ℕ) (h : v % 2 = 0) : (v + 1) / 2 = v / 2 := by
  zify [h]; omega

lemma div2_of_odd (v : ℕ) (h : v % 2 = 1) : (v - 1) / 2 = v / 2 := by
  zify [h]; omega

lemma sibling_parent (v : ℕ) (hv : 1 < v) : (sibling v) / 2 = v / 2 := by
  by_cases h : v % 2 = 0
  · rw [sibling_of_even _ h]; exact div2_of_even _ h
  · rw [sibling_of_odd _ (by omega)]; exact div2_of_odd _ (by omega)

lemma sibling_pos (v : ℕ) (hv : 1 < v) : 0 < sibling v := by
  by_cases h : v % 2 = 0 <;> simp [sibling, h] <;> omega

lemma sibling_gt_one (v : ℕ) (hv : 1 < v) : 1 < sibling v := by
  by_cases h : v % 2 = 0 <;> simp [sibling, h] <;> omega

lemma sibling_in_nodes {n v : ℕ} (hv : v ∈ nodes n) (h1 : 1 < v) :
    sibling v ∈ nodes n := by
  simp [mem_nodes] at hv ⊢
  by_cases h : v % 2 = 0 <;> simp [sibling, h] <;> omega

lemma sibling_left (u : ℕ) : sibling (2 * u) = 2 * u + 1 :=
  sibling_of_even _ (by omega)

lemma sibling_right (u : ℕ) (hu : 0 < u) : sibling (2 * u + 1) = 2 * u :=
  sibling_of_odd _ (by omega)

/-- Dividing `2u` by `2^m` (with `m ≥ 1`) lands at most at `u`. -/
lemma div_pow_le (u m : ℕ) (hm : 0 < m) : (2 * u) / 2 ^ m ≤ u := by
  apply Nat.div_le_of_le_mul
  have hp : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega) 2
  nlinarith

/-- Split off one halving from a power-of-two division. -/
lemma div_pow_split (a k : ℕ) (hk : 0 < k) : a / 2 ^ k = (a / 2) / 2 ^ (k - 1) := by
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have : k = 1 + (k - 1) := by omega
    nth_rw 1 [this]
    rw [pow_add, pow_one]
  rw [hpow, ← Nat.div_div_eq_div_mul]

/-- Dividing `2u+1` by `2^m` (with `m ≥ 1`) lands at most at `u`. -/
lemma div_pow_le' (u m : ℕ) (hm : 0 < m) : (2 * u + 1) / 2 ^ m ≤ u := by
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    calc 2 ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel hm]
      _ = 2 ^ (m - 1) * 2 := pow_succ _ _
      _ = 2 * 2 ^ (m - 1) := by rw [Nat.mul_comm]
  rw [hpow, ← Nat.div_div_eq_div_mul]
  have hdiv2 : (2 * u + 1) / 2 = u := by zify; omega
  rw [hdiv2]
  exact Nat.div_le_self _ _

/-! ## Ancestor lists and paths -/

/-- The ancestors of `v`, from `v` up to the root `1` (empty for `v = 0`). -/
def ancestors : ℕ → List ℕ
  | 0 => []
  | v + 1 => (v + 1) :: ancestors ((v + 1) / 2)
termination_by v => v
decreasing_by omega

@[simp] lemma ancestors_zero : ancestors 0 = [] := ancestors.eq_1

@[simp] lemma ancestors_succ (v : ℕ) :
    ancestors (v + 1) = (v + 1) :: ancestors ((v + 1) / 2) := ancestors.eq_2 v

lemma mem_ancestors {v u : ℕ} : u ∈ ancestors v ↔ 0 < u ∧ ∃ k : ℕ, u = v / 2 ^ k := by
  have h : ∀ u, u ∈ ancestors v ↔ 0 < u ∧ ∃ k : ℕ, u = v / 2 ^ k := by
    induction v using Nat.strongRecOn with
    | ind v ih =>
      cases v with
      | zero =>
        intro u
        simp only [ancestors_zero, List.not_mem_nil]
        constructor
        · intro h; contradiction
        · rintro ⟨hu, k, hk⟩
          simp at hk
          omega
      | succ v =>
        intro u
        simp only [ancestors_succ, List.mem_cons]
        constructor
        · intro h
          rcases h with rfl | h
          · exact ⟨by omega, 0, by simp⟩
          · rcases (ih ((v + 1) / 2) (Nat.div_lt_self (by omega) (by omega)) u).mp h
              with ⟨hu, k, hk⟩
            refine ⟨hu, k + 1, ?_⟩
            rw [hk, Nat.div_div_eq_div_mul]
            congr 1
            rw [pow_succ, Nat.mul_comm]
        · rintro ⟨hu, k, hk⟩
          cases k with
          | zero => left; simp [hk]
          | succ k =>
            right
            have heq : (v + 1) / 2 ^ (k + 1) = ((v + 1) / 2) / 2 ^ k := by
              rw [pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
            rw [hk, heq]
            refine (ih ((v + 1) / 2) (Nat.div_lt_self (by omega) (by omega))
              (((v + 1) / 2) / 2 ^ k)).mpr ⟨?_, k, rfl⟩
            rw [← heq, ← hk]
            exact hu
  exact h u

lemma ancestors_le (v : ℕ) : ∀ u ∈ ancestors v, u ≤ v := by
  intro u hu
  rcases mem_ancestors.mp hu with ⟨_, k, hk⟩
  rw [hk]
  exact Nat.div_le_self _ _

/-- Ancestor lists contain each heap position at most once. -/
lemma ancestors_nodup (v : ℕ) : (ancestors v).Nodup := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    cases v with
    | zero => simp
    | succ v =>
      rw [ancestors_succ, List.nodup_cons]
      constructor
      · intro hmem
        have hle := ancestors_le ((v + 1) / 2) (v + 1) hmem
        omega
      · exact ih ((v + 1) / 2) (Nat.div_lt_self (by omega) (by omega))

/-- A positive heap position has one ancestor at each depth from its own
depth through the root. -/
lemma ancestors_length (v : ℕ) :
    (ancestors v).length = if v = 0 then 0 else Nat.log2 v + 1 := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    cases v with
    | zero => simp
    | succ v =>
      rw [ancestors_succ, List.length_cons]
      rw [if_neg (by omega : v + 1 ≠ 0)]
      by_cases hsmall : v + 1 < 2
      · have hv : v = 0 := by omega
        subst hv
        have hlog : Nat.log2 1 = 0 :=
          (Nat.log2_eq_iff (by decide)).mpr ⟨by norm_num, by norm_num⟩
        norm_num [ancestors, hlog]
      · have htwo : 2 ≤ v + 1 := by omega
        have hdiv : (v + 1) / 2 ≠ 0 := by omega
        have hlog : Nat.log2 (v + 1) = Nat.log2 ((v + 1) / 2) + 1 := by
          rw [Nat.log2_def]
          exact if_pos htwo
        rw [ih ((v + 1) / 2) (Nat.div_lt_self (by omega) (by omega))]
        rw [if_neg hdiv, hlog]

/-- Every positive `ℓ` reaches `1` by repeated halving. -/
lemma exists_div_pow_eq_one (ℓ : ℕ) (hℓ : 0 < ℓ) : ∃ k, ℓ / 2 ^ k = 1 := by
  induction ℓ using Nat.strongRecOn with
  | ind ℓ ih =>
    cases ℓ with
    | zero => contradiction
    | succ ℓ =>
      by_cases h : (ℓ + 1) / 2 = 0
      · exact ⟨0, by omega⟩
      · rcases ih ((ℓ + 1) / 2) (by omega) (by omega) with ⟨k, hk⟩
        exact ⟨k + 1, by
          rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [pow_succ, Nat.mul_comm (2 ^ k) 2]]
          rw [← Nat.div_div_eq_div_mul, hk]⟩

lemma one_mem_ancestors {v : ℕ} (hv : 0 < v) : 1 ∈ ancestors v := by
  rw [mem_ancestors]
  rcases exists_div_pow_eq_one v hv with ⟨k, hk⟩
  exact ⟨by omega, k, by omega⟩

/-! ## Paths in the tree -/

/-- The vertices on the path from leaf `n + i` to the root. -/
def pathOf (n : ℕ) (i : Fin n) : Finset ℕ := (ancestors (n + i.val)).toFinset

/-- The union of all root-to-leaf paths for the opened indices `I`.
Models the `is_node_on_path` array of `mark_paths_to_root` (heap.rs:56-81). -/
def pathSet (n : ℕ) (I : Finset (Fin n)) : Finset ℕ := I.biUnion (pathOf n)

theorem mem_pathOf {n : ℕ} {i : Fin n} {u : ℕ} :
    u ∈ pathOf n i ↔ 0 < u ∧ ∃ k : ℕ, u = (n + i.val) / 2 ^ k := by
  simp [pathOf, mem_ancestors]

theorem mem_pathSet {n : ℕ} {I : Finset (Fin n)} {u : ℕ} :
    u ∈ pathSet n I ↔ ∃ i ∈ I, u ∈ pathOf n i := by
  simp [pathSet]

theorem leaf_mem_pathOf (n : ℕ) (i : Fin n) : n + i.val ∈ pathOf n i := by
  rw [mem_pathOf]
  exact ⟨by omega, 0, by simp⟩

theorem root_mem_pathOf (n : ℕ) (i : Fin n) : 1 ∈ pathOf n i := by
  rw [mem_pathOf]
  rcases exists_div_pow_eq_one (n + i.val) (by omega) with ⟨k, hk⟩
  exact ⟨by omega, k, hk.symm⟩

theorem root_mem_pathSet (n : ℕ) {I : Finset (Fin n)} (hI : I.Nonempty) :
    1 ∈ pathSet n I := by
  rcases hI with ⟨i, hi⟩
  exact mem_pathSet.mpr ⟨i, hi, root_mem_pathOf n i⟩

theorem pathOf_subset_nodes (n : ℕ) (i : Fin n) : pathOf n i ⊆ nodes n := by
  intro u hu
  rcases mem_pathOf.mp hu with ⟨hu, k, hk⟩
  simp [mem_nodes]
  refine ⟨hu, ?_⟩
  rw [hk]
  exact le_trans (Nat.div_le_self _ _) (by omega)

lemma pathOf_mem_nodes_iff {n : ℕ} {i : Fin n} {u : ℕ} (hu : u ∈ pathOf n i) :
    u ∈ Icc 1 (n + i.val) := by
  rcases mem_pathOf.mp hu with ⟨hu, k, hk⟩
  simp
  exact ⟨hu, by rw [hk]; exact Nat.div_le_self _ _⟩

theorem pathSet_subset_nodes (n : ℕ) (I : Finset (Fin n)) : pathSet n I ⊆ nodes n := by
  intro u hu
  rcases mem_pathSet.mp hu with ⟨i, _, hi⟩
  exact pathOf_subset_nodes n i hi

/-- A path has at most `n + i` vertices (crude bound, sufficient for the
trace-size estimates in `Binding.lean`). -/
theorem pathOf_card_le (n : ℕ) (i : Fin n) : (pathOf n i).card ≤ n + i.val := by
  calc (pathOf n i).card
      ≤ (Icc 1 (n + i.val)).card := by
        apply Finset.card_le_card
        intro u hu
        exact pathOf_mem_nodes_iff hu
    _ = n + i.val := by
      simp

/-- Exact number of vertices on a leaf-to-root path. -/
theorem pathOf_card (n : ℕ) (i : Fin n) :
    (pathOf n i).card = Nat.log2 (n + i.val) + 1 := by
  have hpos : n + i.val ≠ 0 := by
    have := i.isLt
    omega
  rw [pathOf, List.toFinset_card_of_nodup (ancestors_nodup _), ancestors_length,
    if_neg hpos]

/-- Every leaf path is bounded by the maximum heap depth. -/
theorem pathOf_card_le_heapDepth (n : ℕ) (i : Fin n) :
    (pathOf n i).card ≤ heapDepth n + 1 := by
  rw [pathOf_card, heapDepth, Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  apply Nat.add_le_add_right
  apply Nat.log_mono_right
  omega

/-- The union of opened paths has at most the sum of their individual path
sizes. -/
theorem pathSet_card_le (n : ℕ) (I : Finset (Fin n)) :
    (pathSet n I).card ≤ I.card * (heapDepth n + 1) := by
  calc
    (pathSet n I).card ≤ ∑ i ∈ I, (pathOf n i).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, (heapDepth n + 1) := by
      exact Finset.sum_le_sum (fun i _ => pathOf_card_le_heapDepth n i)
    _ = I.card * (heapDepth n + 1) := by simp

theorem parent_mem_pathOf {n : ℕ} {i : Fin n} {v : ℕ} (hv : v ∈ pathOf n i) (h1 : 1 < v) :
    v / 2 ∈ pathOf n i := by
  rcases mem_pathOf.mp hv with ⟨hpos, k, hk⟩
  rw [mem_pathOf]
  refine ⟨by omega, k + 1, ?_⟩
  rw [hk, pow_succ, ← Nat.div_div_eq_div_mul]

/-- Ancestors of a path vertex are on the path. -/
theorem ancestor_mem_pathOf {n : ℕ} {i : Fin n} {v u : ℕ} (hv : v ∈ pathOf n i)
    (hu : ∃ k : ℕ, u = v / 2 ^ k) (hpos : 0 < u) : u ∈ pathOf n i := by
  rcases hu with ⟨j, hj⟩
  rcases mem_pathOf.mp hv with ⟨_, k, hk⟩
  rw [mem_pathOf]
  refine ⟨hpos, k + j, ?_⟩
  rw [hj, hk, pow_add, ← Nat.div_div_eq_div_mul]

/-- Two vertices on the same root-leaf path are comparable: one is an ancestor
of the other. -/
theorem comparable_of_mem_pathOf {n : ℕ} {i : Fin n} {a b : ℕ}
    (ha : a ∈ pathOf n i) (hb : b ∈ pathOf n i) :
    (∃ k : ℕ, a = b / 2 ^ k) ∨ (∃ k : ℕ, b = a / 2 ^ k) := by
  rcases mem_pathOf.mp ha with ⟨_, ka, ha⟩
  rcases mem_pathOf.mp hb with ⟨_, kb, hb⟩
  by_cases h : ka ≤ kb
  · right
    exact ⟨kb - ka, by
      have hle : ka + (kb - ka) = kb := by omega
      rw [hb, ha, Nat.div_div_eq_div_mul, ← pow_add, hle]⟩
  · left
    exact ⟨ka - kb, by
      have hle : kb + (ka - kb) = ka := by omega
      rw [ha, hb, Nat.div_div_eq_div_mul, ← pow_add, hle]⟩

/-- The two children of an internal path vertex cannot both continue the
path (siblings are incomparable ancestors of the same leaf). -/
lemma not_both_children_on_pathOf {n : ℕ} {i : Fin n} {u : ℕ} (hu : u ∈ pathOf n i) :
    ¬(2 * u ∈ pathOf n i ∧ 2 * u + 1 ∈ pathOf n i) := by
  intro h
  rcases h with ⟨h2u, h2u1⟩
  have hpos : 0 < u := by
    rcases mem_pathOf.mp h2u with ⟨h2, _, _⟩
    omega
  rcases comparable_of_mem_pathOf h2u h2u1 with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- hm : 2u = (2u+1)/2^m; for m ≥ 1 the RHS is ≤ u, contradiction
    by_cases hmz : m = 0
    · rw [hmz, pow_zero, Nat.div_one] at hm
      omega
    · have hle : 2 * u ≤ u := by
        rw [hm]
        exact div_pow_le' u m (by omega)
      omega
  · -- hm : 2u+1 = (2u)/2^m; same argument
    by_cases hmz : m = 0
    · rw [hmz, pow_zero, Nat.div_one] at hm
      omega
    · have hle : 2 * u + 1 ≤ u := by
        rw [hm]
        exact div_pow_le u m (by omega)
      omega

/-- Exactly one child of an internal path vertex continues the path. -/
theorem child_on_path {n : ℕ} {i : Fin n} {u : ℕ} (hu : u ∈ pathOf n i) (huint : u < n) :
    (2 * u ∈ pathOf n i ∧ 2 * u + 1 ∉ pathOf n i) ∨
    (2 * u ∉ pathOf n i ∧ 2 * u + 1 ∈ pathOf n i) := by
  rcases mem_pathOf.mp hu with ⟨hupos, k, hk⟩
  have hk1 : 0 < k := by
    by_contra hz
    simp at hz
    rw [hz, pow_zero, Nat.div_one] at hk
    omega
  have hchild : (n + i.val) / 2 ^ (k - 1) = 2 * u ∨ (n + i.val) / 2 ^ (k - 1) = 2 * u + 1 := by
    have hdiv : (n + i.val) / 2 ^ (k - 1) / 2 = u := by
      rw [hk, Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hk1]
    omega
  have hmem : (n + i.val) / 2 ^ (k - 1) ∈ pathOf n i := by
    rw [mem_pathOf]
    exact ⟨by omega, k - 1, rfl⟩
  rcases hchild with hc | hc
  · left
    constructor
    · rwa [hc] at hmem
    · exact fun h => not_both_children_on_pathOf hu ⟨by rwa [hc] at hmem, h⟩
  · right
    constructor
    · exact fun h => not_both_children_on_pathOf hu ⟨h, by rwa [hc] at hmem⟩
    · rwa [hc] at hmem

/-! ## Copaths and the frontier -/

/-- The copath of leaf `i`: siblings of the vertices on `path(i)`, excluding
the root. -/
def copathOf (n : ℕ) (i : Fin n) : Finset ℕ :=
  ((pathOf n i).filter (· > 1)).image sibling

def copathSet (n : ℕ) (I : Finset (Fin n)) : Finset ℕ := I.biUnion (copathOf n)

/-- The frontier `F(I) = copath(I) \ path(I)` (`SPEC` Def. 2.3): the vertices
off the opened paths whose parent is on an opened path. `generate_proof`
(heap.rs:117-136) emits exactly these digests, in decreasing heap order. -/
def frontier (n : ℕ) (I : Finset (Fin n)) : Finset ℕ := copathSet n I \ pathSet n I

/-- Canonical proof order: frontier positions in strictly decreasing heap
order, matching the decreasing-parent loop in `generate_proof`. -/
def frontierList (n : ℕ) (I : Finset (Fin n)) : List ℕ :=
  (frontier n I).sort (· ≥ ·)

@[simp] theorem mem_frontierList {n : ℕ} {I : Finset (Fin n)} {v : ℕ} :
    v ∈ frontierList n I ↔ v ∈ frontier n I := by
  simp [frontierList]

@[simp] theorem frontierList_nodup (n : ℕ) (I : Finset (Fin n)) :
    (frontierList n I).Nodup := by
  simp [frontierList]

@[simp] theorem frontierList_length (n : ℕ) (I : Finset (Fin n)) :
    (frontierList n I).length = (frontier n I).card := by
  simp [frontierList]

theorem frontierList_pairwise (n : ℕ) (I : Finset (Fin n)) :
    (frontierList n I).Pairwise (· > ·) := by
  exact List.sortedGT_iff_pairwise.mp (Finset.sortedGT_sort (frontier n I))

theorem mem_copathOf {n : ℕ} {i : Fin n} {v : ℕ} :
    v ∈ copathOf n i ↔ ∃ w ∈ pathOf n i, 1 < w ∧ sibling w = v := by
  simp [copathOf]
  constructor
  · rintro ⟨w, ⟨hw, hgt⟩, hs⟩
    exact ⟨w, hw, hgt, hs⟩
  · rintro ⟨w, hw, hgt, hs⟩
    exact ⟨w, ⟨hw, hgt⟩, hs⟩

theorem mem_copathSet {n : ℕ} {I : Finset (Fin n)} {v : ℕ} :
    v ∈ copathSet n I ↔ ∃ i ∈ I, v ∈ copathOf n i := by
  simp [copathSet]

theorem frontier_disjoint_pathSet (n : ℕ) (I : Finset (Fin n)) :
    Disjoint (frontier n I) (pathSet n I) :=
  sdiff_disjoint

/-- Characterization of the frontier (`SPEC` §2): a vertex is in the frontier
iff it is off the opened paths, in the tree, and its parent is on an opened
path. Mirrors the emit condition of `generate_proof`. -/
theorem mem_frontier_iff {n : ℕ} {I : Finset (Fin n)} {v : ℕ} :
    v ∈ frontier n I ↔ 1 < v ∧ v ∈ nodes n ∧ v ∉ pathSet n I ∧ v / 2 ∈ pathSet n I := by
  constructor
  · intro hv
    simp [frontier] at hv
    rcases hv with ⟨hcop, hnp⟩
    rcases mem_copathSet.mp hcop with ⟨i, hi, hcopi⟩
    rcases mem_copathOf.mp hcopi with ⟨w, hw, hgt, hsw⟩
    have hnodes : w ∈ nodes n := pathOf_subset_nodes n i hw
    refine ⟨by rw [← hsw]; exact sibling_gt_one w hgt,
      by rw [← hsw]; exact sibling_in_nodes hnodes hgt, hnp, ?_⟩
    rw [← hsw, sibling_parent w hgt]
    exact mem_pathSet.mpr ⟨i, hi, parent_mem_pathOf hw hgt⟩
  · rintro ⟨hgt, hnodes, hnp, hpar⟩
    simp [frontier]
    constructor
    · rcases mem_pathSet.mp hpar with ⟨i, hi, hipar⟩
      have hint : v / 2 < n := by
        simp [mem_nodes] at hnodes
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      rcases child_on_path hipar hint with ⟨hon, hoff⟩ | ⟨hoff, hon⟩
      · -- path child is 2*(v/2); since v ∉ pathSet, v is the other child
        have hveq : v = 2 * (v / 2) + 1 := by
          by_contra hne
          have : v = 2 * (v / 2) := by omega
          apply hnp
          rw [this]
          exact mem_pathSet.mpr ⟨i, hi, hon⟩
        apply mem_copathSet.mpr
        refine ⟨i, hi, mem_copathOf.mpr ⟨2 * (v / 2), hon, by omega, ?_⟩⟩
        rw [sibling_left]
        omega
      · -- path child is 2*(v/2)+1
        have hveq : v = 2 * (v / 2) := by
          by_contra hne
          have : v = 2 * (v / 2) + 1 := by omega
          apply hnp
          rw [this]
          exact mem_pathSet.mpr ⟨i, hi, hon⟩
        apply mem_copathSet.mpr
        refine ⟨i, hi, mem_copathOf.mpr ⟨2 * (v / 2) + 1, hon, by omega, ?_⟩⟩
        have : 0 < v / 2 := by omega
        rw [sibling_right _ this]
        omega
    · exact hnp

/-- Leaf positions in `pathSet I` are exactly the opened leaves: an ancestor
of an opened leaf that lies in the leaf layer must be that opened leaf
itself. -/
lemma leaf_pos_of_mem_pathSet {n : ℕ} {I : Finset (Fin n)} {c : ℕ}
    (hc : c ∈ pathSet n I) (hn : n ≤ c) : ∃ i ∈ I, c = n + i.val := by
  rcases mem_pathSet.mp hc with ⟨i, hi, hipath⟩
  rcases mem_pathOf.mp hipath with ⟨_, k, hk⟩
  have hk0 : k = 0 := by
    by_contra hkz
    have : c < n := by
      rw [hk]
      calc (n + i.val) / 2 ^ k
          = ((n + i.val) / 2) / 2 ^ (k - 1) := div_pow_split _ _ (by omega)
        _ ≤ (n + i.val) / 2 := Nat.div_le_self _ _
        _ < n := by
          have := i.isLt
          omega
    omega
  simp [hk0] at hk
  exact ⟨i, hi, hk⟩

/-- Frontier vertices are never opened leaves (they are off the opened
paths). -/
lemma frontier_not_opened_leaf {n : ℕ} {I : Finset (Fin n)} {v : ℕ}
    (hf : v ∈ frontier n I) : ¬∃ i ∈ I, v = n + i.val := by
  rintro ⟨i, hi, rfl⟩
  have : n + i.val ∈ pathSet n I := mem_pathSet.mpr ⟨i, hi, leaf_mem_pathOf n i⟩
  exact (Finset.mem_sdiff.mp hf).2 this

/-- A child of an internal opened-path vertex is either on the opened paths or
in the frontier. This is what makes the bottom-up reconstruction in
`verify_proof` total (heap.rs:203-207). -/
theorem child_of_internal_path {n : ℕ} {I : Finset (Fin n)} {u c : ℕ}
    (hu : u ∈ pathSet n I) (huint : u < n) (hc : c = 2 * u ∨ c = 2 * u + 1) :
    c ∈ pathSet n I ∨ c ∈ frontier n I := by
  by_cases hcpath : c ∈ pathSet n I
  · exact Or.inl hcpath
  · right
    rw [mem_frontier_iff]
    have hunodes : u ∈ nodes n := pathSet_subset_nodes n I hu
    have hu1 : 1 ≤ u := by
      simp [mem_nodes] at hunodes
      omega
    refine ⟨by rcases hc with rfl | rfl <;> omega, ?_, hcpath, ?_⟩
    · simp [mem_nodes]
      rcases hc with rfl | rfl <;> omega
    · rw [show c / 2 = u by rcases hc with rfl | rfl <;> omega]
      exact hu

/-! ## The subtree of a vertex -/

/-- The leaf indices whose leaf lies in the subtree rooted at `v`. -/
def subtreeLeaves (n : ℕ) (v : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v ∈ pathOf n i)

lemma mem_subtreeLeaves {n v : ℕ} {i : Fin n} :
    i ∈ subtreeLeaves n v ↔ v ∈ pathOf n i := by
  simp [subtreeLeaves]

/-- A vertex is on an opened path exactly when its subtree contains an
opened leaf. This is the mathematical meaning of `mark_paths_to_root`. -/
theorem mem_pathSet_iff_subtree_meets {n v : ℕ} {I : Finset (Fin n)} :
    v ∈ pathSet n I ↔ (subtreeLeaves n v ∩ I).Nonempty := by
  constructor
  · intro h
    rcases mem_pathSet.mp h with ⟨i, hi, hv⟩
    exact ⟨i, Finset.mem_inter.mpr ⟨mem_subtreeLeaves.mpr hv, hi⟩⟩
  · rintro ⟨i, hi⟩
    rcases Finset.mem_inter.mp hi with ⟨hv, hI⟩
    exact mem_pathSet.mpr ⟨i, hI, mem_subtreeLeaves.mp hv⟩

/-- Leaf-layer positions on the path union are precisely the opened leaves. -/
theorem leaf_mem_pathSet_iff {n c : ℕ} {I : Finset (Fin n)}
    (hc : n ≤ c) :
    c ∈ pathSet n I ↔ ∃ i ∈ I, c = n + i.val := by
  constructor
  · exact fun h => leaf_pos_of_mem_pathSet h hc
  · rintro ⟨i, hi, rfl⟩
    exact mem_pathSet.mpr ⟨i, hi, leaf_mem_pathOf n i⟩

/-! ## Frontier partition and independence (`SPEC` Lemmas 2.4, 2.5) -/

/-- An unopened leaf is not on any opened path. -/
lemma unopened_leaf_not_in_pathSet {n : ℕ} {I : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ I) : n + j.val ∉ pathSet n I := by
  intro h
  rcases mem_pathSet.mp h with ⟨i, hi, hipath⟩
  rcases mem_pathOf.mp hipath with ⟨_, k, hk⟩
  have hk0 : k = 0 := by
    by_contra hkz
    have hkpos : 0 < k := by omega
    have : (n + i.val) / 2 ^ k < n := by
      calc (n + i.val) / 2 ^ k
          = ((n + i.val) / 2) / 2 ^ (k - 1) := by
            rw [show 2 ^ k = 2 * 2 ^ (k - 1) by
              calc 2 ^ k = 2 ^ ((k - 1) + 1) := by rw [Nat.sub_add_cancel hkpos]
                _ = 2 ^ (k - 1) * 2 := pow_succ _ _
                _ = 2 * 2 ^ (k - 1) := by rw [Nat.mul_comm]]
            rw [← Nat.div_div_eq_div_mul]
        _ ≤ (n + i.val) / 2 := Nat.div_le_self _ _
        _ < n := by
          have : i.val < n := i.isLt
          omega
    omega
  simp [hk0] at hk
  have hij : i = j := leaf_pos_inj (by omega)
  exact hj (hij ▸ hi)

/-- The frontier subtrees cover exactly the unopened leaves
(`SPEC` Lemma 2.4, covering direction). -/
theorem unopened_leaf_in_frontier_subtree {n : ℕ} {I : Finset (Fin n)} {j : Fin n}
    (hn : 0 < n) (hI : I.Nonempty) (hj : j ∉ I) :
    ∃ v ∈ frontier n I, j ∈ subtreeLeaves n v := by
  -- Walk up from leaf ℓ = n+j: ℓ itself is off the opened paths, the root is
  -- on them, so there is a first level (from the root down) whose ancestor of
  -- ℓ is back off the paths; its parent is on the paths, so it is frontier.
  set ℓ := n + j.val
  have hleaf : ℓ ∉ pathSet n I := unopened_leaf_not_in_pathSet hj
  have hex : ∃ k, ℓ / 2 ^ k ∈ pathSet n I := by
    rcases exists_div_pow_eq_one ℓ (by omega) with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; exact root_mem_pathSet n hI⟩
  let k := Nat.find hex
  have hk : ℓ / 2 ^ k ∈ pathSet n I := Nat.find_spec hex
  have hkmin : ∀ m < k, ℓ / 2 ^ m ∉ pathSet n I :=
    fun m hm => Nat.find_min hex hm
  have hkpos : 0 < k := by
    by_contra hz
    simp at hz
    exact hleaf (by simpa [hz] using hk)
  set v := ℓ / 2 ^ (k - 1) with hvdef
  have hvoff : v ∉ pathSet n I := hkmin (k - 1) (by omega)
  have hvpar : v / 2 ∈ pathSet n I := by
    have : ℓ / 2 ^ k = v / 2 := by
      rw [hvdef, Nat.div_div_eq_div_mul, ← pow_succ,
        Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rwa [← this]
  have hvgt1 : 1 < v := by
    rcases mem_pathSet.mp hvpar with ⟨i, hi, hi'⟩
    have := pathOf_subset_nodes n i hi'
    simp [mem_nodes] at this
    omega
  have hvfront : v ∈ frontier n I := by
    rw [mem_frontier_iff]
    refine ⟨hvgt1, ?_, hvoff, hvpar⟩
    rw [mem_nodes, hvdef]
    exact ⟨by omega, le_trans (Nat.div_le_self ℓ (2 ^ (k - 1))) (by omega)⟩
  exact ⟨v, hvfront, by
    rw [mem_subtreeLeaves, mem_pathOf]
    refine ⟨by omega, k - 1, ?_⟩
    rw [hvdef]⟩

/-- The frontier subtrees are pairwise disjoint (`SPEC` Lemma 2.5 = notes
Claim 18.6.7; holds for any binary tree). -/
theorem frontier_subtrees_disjoint {n : ℕ} {I : Finset (Fin n)} {v₁ v₂ : ℕ}
    (h₁ : v₁ ∈ frontier n I) (h₂ : v₂ ∈ frontier n I) (hne : v₁ ≠ v₂) :
    Disjoint (subtreeLeaves n v₁) (subtreeLeaves n v₂) := by
  rw [Finset.disjoint_left]
  intro j hj₁ hj₂
  simp [mem_subtreeLeaves] at hj₁ hj₂
  rcases mem_frontier_iff.mp h₁ with ⟨hgt₁, _, hnpath₁, _⟩
  rcases mem_frontier_iff.mp h₂ with ⟨hgt₂, _, hnpath₂, _⟩
  -- both v₁ and v₂ are ancestors of leaf n+j, hence comparable
  rcases comparable_of_mem_pathOf hj₁ hj₂ with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- v₁ is an ancestor of v₂, properly (v₁ ≠ v₂), hence an ancestor of
    -- the parent of v₂, which lies on the opened paths: contradiction.
    have hm0 : 0 < m := by
      by_contra hz
      simp at hz
      rw [hz, pow_zero, Nat.div_one] at hm
      exact hne hm
    rcases mem_frontier_iff.mp h₂ with ⟨_, _, _, hpar₂⟩
    rcases mem_pathSet.mp hpar₂ with ⟨i, hi, hi₂⟩
    have hv₁par : v₁ ∈ pathOf n i := by
      apply ancestor_mem_pathOf hi₂ ⟨m - 1, ?_⟩ (by omega)
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        have : m = 1 + (m - 1) := by omega
        nth_rw 1 [this]
        rw [pow_add, pow_one]
      rw [hm, hpow, ← Nat.div_div_eq_div_mul]
    exact hnpath₁ (mem_pathSet.mpr ⟨i, hi, hv₁par⟩)
  · -- symmetric
    have hm0 : 0 < m := by
      by_contra hz
      simp at hz
      rw [hz, pow_zero, Nat.div_one] at hm
      exact hne hm.symm
    rcases mem_frontier_iff.mp h₁ with ⟨_, _, _, hpar₁⟩
    rcases mem_pathSet.mp hpar₁ with ⟨i, hi, hi₁⟩
    have hv₂par : v₂ ∈ pathOf n i := by
      apply ancestor_mem_pathOf hi₁ ⟨m - 1, ?_⟩ (by omega)
      have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
        have : m = 1 + (m - 1) := by omega
        nth_rw 1 [this]
        rw [pow_add, pow_one]
      rw [hm, hpow, ← Nat.div_div_eq_div_mul]
    exact hnpath₂ (mem_pathSet.mpr ⟨i, hi, hv₂par⟩)

/-- The frontier partition (`SPEC` Lemma 2.4): the subtrees rooted at the
frontier vertices partition the unopened leaves. -/
theorem frontier_partition (n : ℕ) (I : Finset (Fin n)) (hn : 0 < n) (hI : I.Nonempty) :
    (frontier n I).biUnion (subtreeLeaves n) =
      Finset.univ.filter (fun i : Fin n => i ∉ I) := by
  ext j
  simp
  constructor
  · rintro ⟨v, hvf, hjv⟩ hjI
    simp [mem_subtreeLeaves] at hjv
    have : v ∈ pathSet n I := mem_pathSet.mpr ⟨j, hjI, hjv⟩
    exact (mem_frontier_iff.mp hvf).2.2.1 this
  · intro hjI
    rcases unopened_leaf_in_frontier_subtree hn hI hjI with ⟨v, hvf, hjv⟩
    exact ⟨v, hvf, hjv⟩

/-- The sum of the frontier subtree leaf-counts is `n - |I|` (the number of
unopened leaves). Used for the tight `(n - q)` coefficient in the hiding
bound (`SPEC` Theorem 9.2). -/
theorem frontier_leaf_sum (n : ℕ) (I : Finset (Fin n)) (hn : 0 < n)
    (hI : I.Nonempty) :
    ∑ v ∈ frontier n I, (subtreeLeaves n v).card = n - I.card := by
  have hpart := frontier_partition n I hn hI
  calc ∑ v ∈ frontier n I, (subtreeLeaves n v).card
      = ((frontier n I).biUnion (subtreeLeaves n)).card := by
        have hdisj : Set.PairwiseDisjoint (↑(frontier n I)) (subtreeLeaves n) := by
          intro v hv v' hv' hne
          exact frontier_subtrees_disjoint hv hv' hne
        rw [← Finset.card_biUnion hdisj]
    _ = (Finset.univ.filter (fun i : Fin n => i ∉ I)).card := by rw [hpart]
    _ = n - I.card := by
      classical
      have : Finset.univ.filter (fun i : Fin n => i ∉ I) = Finset.univ \ I := by
        ext x
        simp
      rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ I),
        Finset.card_univ, Fintype.card_fin]

end Heap
