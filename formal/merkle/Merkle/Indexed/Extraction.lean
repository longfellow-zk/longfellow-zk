import Merkle.Indexed.Codec
import Merkle.QueryTable

/-! Extract a column by following its heap ancestors in the original query
table. This uses the shared table-uniqueness and heap lemmas; it does not copy
the legacy partial-tree extractor. The table and root alone fix every column,
before any opening challenge is read. -/
namespace Merkle.Indexed
open Finset QueryTable

variable {Salt M D Enc : Type*} [DecidableEq D]
variable {codec : Codec Salt M D Enc}

/-- Recover the label of one vertex. The decoder receives the parent index
from the heap relation, so a node from another position cannot be grafted in. -/
def label (dec : RoleDecoders codec) (trace : List (Enc × D)) (root : D) (vertex : ℕ) : Option D :=
  if vertex = 0 then none
  else if vertex = 1 then some root
  else match label dec trace root (vertex/2) with
    | none => none
    | some parent => match preimage trace parent with
      | none => none
      | some raw => match dec.nodeDec (vertex/2) raw with
        | none => none
        | some pair => some (if vertex % 2 = 0 then pair.1 else pair.2)
termination_by vertex
decreasing_by omega

def column (dec : RoleDecoders codec) (trace : List (Enc × D)) (root : D)
    {n : ℕ} (index : Fin n) : Option (Salt × M) :=
  match label dec trace root (n+index.val) with
  | none => none
  | some digest => match preimage trace digest with
    | none => none
    | some raw => dec.leafDec raw

def messages [Inhabited M] (dec : RoleDecoders codec) (trace : List (Enc × D))
    (root : D) (n : ℕ) : Fin n → M :=
  fun index => ((column dec trace root index).map Prod.snd).getD default

variable [Inhabited D] (S : Scheme Salt M D Enc)

/-- The required inputs are exactly the opened leaves and internal vertices
on their paths. Frontier labels are supplied by the opening, not queried. -/
def ContainsOpening (n : ℕ) (I : Finset (Fin n)) (a : Fin n → M)
    (proof : Opening n I Salt D) (trace : List (Enc × D)) : Prop :=
  (∀ i (member : i ∈ I),
    (S.leafEnc (proof.nonce ⟨i,member⟩,a i),checkValues S n I a proof (n+i.val)) ∈ trace) ∧
  (∀ v, 0 < v → v < n → v ∈ Heap.pathSet n I →
    (S.nodeEnc v (checkValues S n I a proof (2*v),checkValues S n I a proof (2*v+1)),
      checkValues S n I a proof v) ∈ trace)

theorem label_eq_checkValues (dec : RoleDecoders S.toCodec)
    {n : ℕ} (root : D) (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)
    (trace : List (Enc × D)) (unique : MH.CollisionFree trace)
    (accepted : Accepts S n root I a proof) (contains : ContainsOpening S n I a proof trace)
    (vertex : ℕ) (onPath : vertex ∈ Heap.pathSet n I) :
    label dec trace root vertex = some (checkValues S n I a proof vertex) := by
  induction vertex using Nat.strong_induction_on with
  | h vertex ih =>
      have bounds := Heap.pathSet_subset_nodes n I onPath
      have positive : 0 < vertex := Heap.pos_of_mem_nodes bounds
      have below : vertex < 2*n := by
        have := Heap.mem_nodes.mp bounds
        have := accepted.1
        omega
      by_cases atRoot : vertex = 1
      · subst vertex
        rw [label,if_neg (by decide : (1 : ℕ) ≠ 0),if_pos rfl,accepted.2]
      · obtain ⟨i,member,path⟩ := Heap.mem_pathSet.mp onPath
        have parentPath : vertex/2 ∈ Heap.pathSet n I :=
          Heap.mem_pathSet.mpr ⟨i,member,Heap.parent_mem_pathOf path (by omega)⟩
        have parent := ih (vertex/2) (by omega) parentPath
        let pair := (checkValues S n I a proof (2*(vertex/2)),
          checkValues S n I a proof (2*(vertex/2)+1))
        have queried := contains.2 (vertex/2) (by omega) (by omega) parentPath
        have found := preimage_of_mem trace unique (S.nodeEnc (vertex/2) pair)
          (checkValues S n I a proof (vertex/2)) queried
        rw [label,if_neg (by omega),if_neg atRoot,parent]
        simp only [found,dec.node_roundTrip]
        rcases Nat.mod_two_eq_zero_or_one vertex with even | odd
        · simp only [even,if_true,pair,show 2*(vertex/2) = vertex by omega]
        · simp only [odd,show (1 : ℕ) ≠ 0 by decide,if_false,pair,
            show 2*(vertex/2)+1 = vertex by omega]

theorem column_eq_opened (dec : RoleDecoders S.toCodec)
    {n : ℕ} (root : D) (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)
    (trace : List (Enc × D)) (unique : MH.CollisionFree trace)
    (accepted : Accepts S n root I a proof) (contains : ContainsOpening S n I a proof trace)
    (i : Fin n) (member : i ∈ I) :
    column dec trace root i = some (proof.nonce ⟨i,member⟩,a i) := by
  have path : n+i.val ∈ Heap.pathSet n I :=
    Heap.mem_pathSet.mpr ⟨i,member,Heap.leaf_mem_pathOf n i⟩
  rw [column,label_eq_checkValues S dec root I a proof trace unique accepted contains _ path]
  simp only [preimage_of_mem trace unique _ _ (contains.1 i member),dec.leaf_roundTrip]

theorem messages_agree [Inhabited M] (dec : RoleDecoders S.toCodec)
    {n : ℕ} (root : D) (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)
    (trace : List (Enc × D)) (unique : MH.CollisionFree trace)
    (accepted : Accepts S n root I a proof) (contains : ContainsOpening S n I a proof trace) :
    ∀ i ∈ I, messages dec trace root n i = a i := by
  intro i member
  rw [messages,column_eq_opened S dec root I a proof trace unique accepted contains i member]
  rfl

end Merkle.Indexed
