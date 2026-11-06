import Merkle.Heap

/-!
# Deterministic core of the Merkle-heap commitment

This file models the mathematical core of
`rust/runtime/v1/merkle.rs` and `rust/runtime/merkle/src/heap.rs`. Wire-format list parsing and
`MerkleError` branches are refined separately in `Wire.lean`.

Leaf and internal inputs are encoded into one common type `Enc`. No
leaf/internal range-disjointness is assumed. Encoding injectivity is not
needed for completeness; it enters only in `Collision.lean`.
-/

open Finset Nat Heap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Merkle

namespace MH

universe uSalt uMsg uDigest uEnc

variable {Salt : Type uSalt} {M : Type uMsg} {D : Type uDigest}
variable {Enc : Type uEnc}

/-- Mathematical opening data contains exactly the nonce and frontier
coordinates consumed for `I`; there are no irrelevant total-function
coordinates. -/
structure Opening (n : ℕ) (I : Finset (Fin n)) (Salt : Type uSalt)
    (D : Type uDigest) where
  nonce : (i : {i : Fin n // i ∈ I}) → Salt
  frontierValue : (v : {v : ℕ // v ∈ Heap.frontier n I}) → D

/-! ## Role encodings and hash scheme -/

/-- The two role serializations.  They are fixed protocol geometry and never
depend on the oracle, which is why they are kept apart from the hash: an
oracle-indexed family of schemes is `fun ω => C.withOracle (oracle ω)`, a
construction that cannot accidentally vary the encodings. -/
structure Codec (Salt : Type uSalt) (M : Type uMsg) (D : Type uDigest)
    (Enc : Type uEnc) where
  leafEnc : Salt × M → Enc
  nodeEnc : D × D → Enc

/-- A codec together with the hash its outputs are fed to. -/
structure Scheme (Salt : Type uSalt) (M : Type uMsg) (D : Type uDigest)
    (Enc : Type uEnc) extends Codec Salt M D Enc where
  H : Enc → D

/-- Pair fixed encodings with a given oracle. -/
def Codec.withOracle (C : Codec Salt M D Enc) (H : Enc → D) :
    Scheme Salt M D Enc where
  toCodec := C
  H := H

/-- Both role encodings are injective.  Range *overlap* between the two roles
stays permitted (the concrete untagged codec of `Instantiate.lean` has it);
only same-role injectivity is ever used. -/
structure Codec.Inj (C : Codec Salt M D Enc) : Prop where
  leaf : Function.Injective C.leafEnc
  node : Function.Injective C.nodeEnc

variable (S : Scheme Salt M D Enc)
variable [Inhabited D]

/-! ## Whole-tree commitment labels -/

/-- Bottom-up heap labels. The rank `2*n-v` strictly decreases when an
internal position recurses to either child. -/
def commitLabels (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M) (v : ℕ) : D :=
  if hleaf : n ≤ v ∧ v < 2 * n then
    S.H (S.leafEnc (nonce ⟨v - n, by omega⟩, m ⟨v - n, by omega⟩))
  else if hint : 0 < v ∧ v < n then
    S.H (S.nodeEnc
      (commitLabels n nonce m (2 * v), commitLabels n nonce m (2 * v + 1)))
  else
    default
termination_by 2 * n - v
decreasing_by all_goals omega

/-- Root digest of a committed heap. -/
def root (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M) : D :=
  commitLabels S n nonce m 1

theorem commitLabels_leaf (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M)
    (v : ℕ) (h : n ≤ v ∧ v < 2 * n) :
    commitLabels S n nonce m v =
      S.H (S.leafEnc (nonce ⟨v - n, by omega⟩, m ⟨v - n, by omega⟩)) := by
  rw [commitLabels]; simp [h]

theorem commitLabels_leaf_pos (n : ℕ) (nonce : Fin n → Salt)
    (m : Fin n → M) (i : Fin n) :
    commitLabels S n nonce m (n + i.val) =
      S.H (S.leafEnc (nonce i, m i)) := by
  rw [commitLabels_leaf S n nonce m _ (by omega)]
  simp

theorem commitLabels_node (n : ℕ) (nonce : Fin n → Salt) (m : Fin n → M)
    (v : ℕ) (h : 0 < v ∧ v < n) :
    commitLabels S n nonce m v =
      S.H (S.nodeEnc
        (commitLabels S n nonce m (2 * v),
         commitLabels S n nonce m (2 * v + 1))) := by
  rw [commitLabels]; simp [show ¬(n ≤ v ∧ v < 2 * n) by omega, h]

/-! ## Exact honest openings -/

/-- Restrict the honest nonces and heap labels to exactly the coordinates in
an opening. -/
def openCore (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) : Opening n I Salt D where
  nonce i := nonce i.val
  frontierValue v := commitLabels S n nonce m v.val

/-! ## Verifier reconstruction -/

/-- Bottom-up values assigned by the core verifier. Opened leaves are
recomputed, frontier vertices are supplied by the exact proof, and internal
path vertices are hashed. -/
def checkValues (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (v : ℕ) : D :=
  if hleaf : n ≤ v ∧ v < 2 * n then
    if hi : (⟨v - n, by omega⟩ : Fin n) ∈ I then
      S.H (S.leafEnc (pf.nonce ⟨_, hi⟩, a ⟨v - n, by omega⟩))
    else if hfront : v ∈ Heap.frontier n I then
      pf.frontierValue ⟨v, hfront⟩
    else
      default
  else if hfront : v ∈ Heap.frontier n I then
    pf.frontierValue ⟨v, hfront⟩
  else if hpath : 0 < v ∧ v < n ∧ v ∈ Heap.pathSet n I then
    S.H (S.nodeEnc
      (checkValues n I a pf (2 * v), checkValues n I a pf (2 * v + 1)))
  else
    default
termination_by 2 * n - v
decreasing_by all_goals omega

theorem checkValues_leaf (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (i : Fin n) (hi : i ∈ I) :
    checkValues S n I a pf (n + i.val) =
      S.H (S.leafEnc (pf.nonce ⟨i, hi⟩, a i)) := by
  rw [checkValues]
  simp [show n ≤ n + i.val ∧ n + i.val < 2 * n by omega, hi]

theorem checkValues_frontier (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (v : ℕ) (hv : v ∈ Heap.frontier n I) :
    checkValues S n I a pf v =
      pf.frontierValue ⟨v, hv⟩ := by
  rw [checkValues]
  split
  · rename_i hleaf
    have hi : (⟨v - n, by omega⟩ : Fin n) ∉ I := fun hmem =>
      Heap.frontier_not_opened_leaf hv
        ⟨_, hmem, (Nat.add_sub_cancel' hleaf.1).symm⟩
    simp [hi]
  · simp

theorem checkValues_node (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) (v : ℕ)
    (hv : 0 < v ∧ v < n ∧ v ∈ Heap.pathSet n I) :
    checkValues S n I a pf v =
      S.H (S.nodeEnc
        (checkValues S n I a pf (2 * v),
         checkValues S n I a pf (2 * v + 1))) := by
  rw [checkValues]
  have hfront : v ∉ Heap.frontier n I := fun hf =>
    (Finset.disjoint_left.mp (Heap.frontier_disjoint_pathSet n I)) hf hv.2.2
  simp [show ¬(n ≤ v ∧ v < 2 * n) by omega, hfront, hv]

/-- Core acceptance: the query set is nonempty and the reconstructed root is
the claimed root. Shape/list errors belong to `checkWire`. -/
def Accepts (n : ℕ) (rt : D) (I : Finset (Fin n)) (a : Fin n → M)
    (pf : Opening n I Salt D) : Prop :=
  I.Nonempty ∧ checkValues S n I a pf 1 = rt

/-! ## Completeness -/

private theorem values_agree (n : ℕ) (I : Finset (Fin n))
    (nonce : Fin n → Salt) (m : Fin n → M) :
    ∀ v, v ∈ Heap.pathSet n I →
      checkValues S n I m
          (openCore S n I nonce m) v =
        commitLabels S n nonce m v := by
  intro v
  refine WellFounded.induction (measure (fun v : ℕ => 2 * n - v)).wf v
    (C := fun v => v ∈ Heap.pathSet n I →
      checkValues S n I m
          (openCore S n I nonce m) v =
        commitLabels S n nonce m v) ?_
  intro v ih hmem
  by_cases hge : n ≤ v
  · rcases Heap.leaf_pos_of_mem_pathSet hmem hge with ⟨i, hi, rfl⟩
    rw [checkValues_leaf S n I m _ i hi,
      commitLabels_leaf_pos S n nonce m i]
    rfl
  · have hpos : 0 < v := Heap.pos_of_mem_nodes (Heap.pathSet_subset_nodes n I hmem)
    have hvlt : v < n := by omega
    rw [checkValues_node S n I m _ v ⟨hpos, hvlt, hmem⟩,
      commitLabels_node S n nonce m v ⟨hpos, hvlt⟩]
    apply congrArg S.H
    apply congrArg S.nodeEnc
    apply Prod.ext
    · rcases Heap.child_of_internal_path hmem hvlt (Or.inl rfl) with hc | hc
      · exact ih (2 * v) (by change 2 * n - 2 * v < 2 * n - v; omega) hc
      · rw [checkValues_frontier S n I m _ (2 * v) hc]
        simp [openCore]
    · rcases Heap.child_of_internal_path hmem hvlt (Or.inr rfl) with hc | hc
      · exact ih (2 * v + 1)
          (by change 2 * n - (2 * v + 1) < 2 * n - v; omega) hc
      · rw [checkValues_frontier S n I m _ (2 * v + 1) hc]
        simp [openCore]

/-- Honest core openings verify (`SPEC.md` Lemma 6.1). -/
theorem mh_core_completeness (n : ℕ) (I : Finset (Fin n))
    (hI : I.Nonempty) (nonce : Fin n → Salt) (m : Fin n → M) :
    Accepts S n (root S n nonce m) I m
      (openCore S n I nonce m) := by
  constructor
  · exact hI
  · exact values_agree S n I nonce m 1
      (Heap.root_mem_pathSet n hI)

end MH

end Merkle
