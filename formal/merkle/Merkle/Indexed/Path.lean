import Merkle.Indexed.Extraction
import Merkle.Indexed.Independence
import Merkle.Indexed.Execution

/-! One selected opened column suffices to expose disagreement with the
original-table extraction. Its target at each heap position is recovered
from that table alone, before any new authentication hash is evaluated. -/
namespace Merkle.Indexed
open QueryTable
open scoped Classical

variable {Salt M D Enc : Type} [DecidableEq D] [Inhabited D]
variable (codec : Codec Salt M D Enc) (dec : RoleDecoders codec)
variable {n : ℕ} (I : Finset (Fin n)) (a : Fin n → M) (proof : Opening n I Salt D)
variable (index : Fin n) (opened : index ∈ I)

omit [Inhabited D] in
/-- Every non-root target is a child digest already present in an original
query input. This identifies the existing receiving-query charge when that
child is hashed only after the extraction cut. -/
theorem label_named (trace : List (Enc × D)) (root digest : D) (vertex : ℕ)
    (found : label dec trace root vertex = some digest) :
    digest = root ∨ ∃ raw answer children,
      (raw,answer) ∈ trace ∧ dec.nodeDec (vertex/2) raw = some children ∧
        (digest = children.1 ∨ digest = children.2) := by
  unfold label at found
  split at found
  · cases found
  · split at found
    · exact Or.inl (Option.some.inj found).symm
    · split at found
      · cases found
      · rename_i parent parentFound
        split at found
        · cases found
        · rename_i raw inputFound
          split at found
          · cases found
          · rename_i children decoded
            refine Or.inr ⟨raw,parent,children,preimage_mem trace parent raw inputFound,decoded,?_⟩
            split at found
            · exact Or.inl (Option.some.inj found).symm
            · exact Or.inr (Option.some.inj found).symm

def pathInput (H : Enc → D) (vertex : ℕ) : Enc :=
  if vertex < n then nodeInput codec n I a proof H vertex
  else codec.leafEnc (proof.nonce ⟨index,opened⟩,a index)

theorem path_leaf_unique (vertex : ℕ) (member : vertex ∈ Heap.pathOf n index)
    (leaf : n ≤ vertex) : vertex = n+index.val := by
  obtain ⟨_,power,equal⟩ := Heap.mem_pathOf.mp member
  cases power with
  | zero => simpa only [pow_zero,Nat.div_one] using equal
  | succ power =>
      have bound : vertex ≤ (n+index.val)/2 := by
        rw [equal,Heap.div_pow_split _ _ (by omega)]
        exact Nat.div_le_self _ _
      have := index.isLt
      omega

omit [DecidableEq D] in
theorem pathInput_answer (H : Enc → D) (vertex : ℕ) (member : vertex ∈ Heap.pathOf n index) :
    H (pathInput codec I a proof index opened H vertex) =
      checkValues (codec.withOracle H) n I a proof vertex := by
  by_cases internal : vertex < n
  · rw [pathInput,if_pos internal,checkValues_node]
    · rfl
    · exact ⟨Heap.pos_of_mem_nodes (Heap.pathOf_subset_nodes n index member),internal,
        Heap.mem_pathSet.mpr ⟨index,opened,member⟩⟩
  · have same := path_leaf_unique index vertex member (by omega)
    rw [pathInput,if_neg internal,same,checkValues_leaf _ _ _ _ _ index opened]
    rfl

omit [DecidableEq D] in
theorem pathInput_off (separated : Separated codec n) (H H' : Enc → D)
    (vertex : ℕ) (positive : 0 < vertex)
    (agree : Bcs.TotalOracle.AgreeOff (pathInput codec I a proof index opened H vertex) H H') :
    pathInput codec I a proof index opened H vertex = pathInput codec I a proof index opened H' vertex := by
  by_cases internal : vertex < n
  · simp only [pathInput,if_pos internal] at agree ⊢
    exact nodeInput_off codec n I a proof separated H H' vertex positive internal agree
  · simp only [pathInput,if_neg internal]

omit [DecidableEq D] in
/-- The selected path uses the verifier's existing indexed hash calls.
Selection itself adds no authentication query. -/
theorem pathInput_visible (H : Enc → D) (vertex : ℕ)
    (member : vertex ∈ Heap.pathOf n index) :
    (pathInput codec I a proof index opened H vertex,
      H (pathInput codec I a proof index opened H vertex)) ∈
        ((check codec n I a proof).run H).2 := by
  have bounds := Heap.mem_nodes.mp (Heap.pathOf_subset_nodes n index member)
  have inPath := Heap.mem_pathSet.mpr ⟨index,opened,member⟩
  have notFrontier : vertex ∉ Heap.frontier n I := by
    intro frontier
    exact (Heap.mem_frontier_iff.mp frontier).2.2.1 inPath
  apply check_visible codec n I a proof H vertex _ (by omega) (by omega)
  by_cases internal : vertex < n
  · simp only [operation,show ¬(n ≤ vertex ∧ vertex < 2*n) by omega,↓reduceDIte,
      notFrontier,show 0 < vertex ∧ vertex < n ∧ vertex ∈ Heap.pathSet n I from
        ⟨by omega,internal,inPath⟩,and_self,if_true,pathInput,nodeInput]
  · have atLeaf := path_leaf_unique index vertex member (by omega)
    subst vertex
    simp only [operation,show n ≤ n+index.val ∧ n+index.val < 2*n from
      ⟨by omega,by have := index.isLt; omega⟩,↓reduceDIte,Nat.add_sub_cancel_left,
      show (⟨index.val,by omega⟩ : Fin n) = index from Fin.ext rfl,opened,
      and_self,pathInput,if_neg (by omega : ¬n+index.val < n)]

/-- Propagate the root label down a single path. The no-hit condition says
that a node whose answer matches its recovered target is already in the
original table. Only original-table collision freedom is used. -/
theorem path_labels (H : Enc → D) (trace : List (Enc × D)) (root : D)
    (unique : MH.CollisionFree trace) (accepted : Accepts (codec.withOracle H) n root I a proof)
    (known : ∀ vertex ∈ Heap.pathOf n index,
      label dec trace root vertex = some (checkValues (codec.withOracle H) n I a proof vertex) →
      (pathInput codec I a proof index opened H vertex,
        checkValues (codec.withOracle H) n I a proof vertex) ∈ trace) :
    ∀ vertex ∈ Heap.pathOf n index,
      label dec trace root vertex = some (checkValues (codec.withOracle H) n I a proof vertex) := by
  intro vertex
  induction vertex using Nat.strong_induction_on with
  | h vertex ih =>
      intro member
      have bounds := Heap.mem_nodes.mp (Heap.pathOf_subset_nodes n index member)
      have positive : 0 < vertex := by omega
      have below : vertex < 2*n := by have := index.isLt; omega
      by_cases atRoot : vertex = 1
      · subst vertex
        rw [label,if_neg (by decide : (1 : ℕ) ≠ 0),if_pos rfl,accepted.2]
      · have parentPath := Heap.parent_mem_pathOf member (by omega)
        have parentLabel := ih (vertex/2) (by omega) parentPath
        have parentQuery := known (vertex/2) parentPath parentLabel
        have internal : vertex/2 < n := by omega
        simp only [pathInput,if_pos internal,nodeInput] at parentQuery
        have found := preimage_of_mem trace unique _ _ parentQuery
        rw [label,if_neg (by omega),if_neg atRoot,parentLabel]
        simp only [found,dec.node_roundTrip]
        rcases Nat.mod_two_eq_zero_or_one vertex with even | odd
        · simp only [even,if_true,show 2*(vertex/2) = vertex by omega]
        · simp only [odd,show (1 : ℕ) ≠ 0 by decide,if_false,
            show 2*(vertex/2)+1 = vertex by omega]

theorem column_agreement [Inhabited M] (H : Enc → D) (trace : List (Enc × D)) (root : D)
    (unique : MH.CollisionFree trace) (accepted : Accepts (codec.withOracle H) n root I a proof)
    (known : ∀ vertex ∈ Heap.pathOf n index,
      label dec trace root vertex = some (checkValues (codec.withOracle H) n I a proof vertex) →
      (pathInput codec I a proof index opened H vertex,
        checkValues (codec.withOracle H) n I a proof vertex) ∈ trace) :
    messages dec trace root n index = a index := by
  have member := Heap.leaf_mem_pathOf n index
  have label := path_labels codec dec I a proof index opened H trace root unique accepted known
    (n+index.val) member
  have query := known _ member label
  simp only [pathInput,if_neg (by omega : ¬n+index.val < n)] at query
  have found := preimage_of_mem trace unique _ _ query
  simp only [messages,column,label,found,dec.leaf_roundTrip,Option.map_some,Option.getD_some]

/-- A disagreeing opened column gives a missing query on its own path
whose answer equals the one original-table target for that position. -/
theorem disagreement_hit [Inhabited M] (H : Enc → D) (trace : List (Enc × D)) (root : D)
    (unique : MH.CollisionFree trace) (accepted : Accepts (codec.withOracle H) n root I a proof)
    (different : messages dec trace root n index ≠ a index) :
    ∃ vertex ∈ Heap.pathOf n index,
      (pathInput codec I a proof index opened H vertex,
        checkValues (codec.withOracle H) n I a proof vertex) ∉ trace ∧
      label dec trace root vertex = some (H (pathInput codec I a proof index opened H vertex)) := by
  by_contra absent
  apply different
  apply column_agreement codec dec I a proof index opened H trace root unique accepted
  intro vertex member target
  by_contra missing
  apply absent
  exact ⟨vertex,member,missing,by rwa [pathInput_answer codec I a proof index opened H vertex member]⟩

end Merkle.Indexed
