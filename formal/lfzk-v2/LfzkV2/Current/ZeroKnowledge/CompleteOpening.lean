import LfzkV2.Current.OpeningBody
import LfzkV2.Joint.Honest

/-! Honest authentication in the actual sampled-order wire layout. The
query positions come from the opening oracle; only nonce and frontier values
are serialized. Reconstructing them checks the original commitment root. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteOpening

open Merkle Merkle.MH Merkle.RandomOracle LigeroFamily
open scoped Classical

variable {Salt Nonce Leaf D Enc : Type} [Inhabited D] [Inhabited Leaf]
variable {n t : ℕ}

def raw (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OrderedOpening.Raw t Nonce Leaf D where
  values i := columns (indices i)
  nonce i := nonces (indices i)
  frontier := (Heap.frontierList n (OrderedOpening.query indices).coordinates).map
    (commitLabels scheme n (fun i => bind i (nonces i)) columns)

omit [Inhabited Leaf] in
theorem raw_frontier_bound (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    (raw scheme bind indices nonces columns).frontier.length ≤ t*(Heap.heapDepth n+1) := by
  have bound := Heap.frontier_card_le n (OrderedOpening.query indices).coordinates
  simpa only [raw,List.length_map,Heap.frontierList_length,QuerySet.card_coordinates] using bound

def claim (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OpeningClaim n Salt Leaf D where
  I := (OrderedOpening.query indices).coordinates
  a i := if i ∈ (OrderedOpening.query indices).coordinates then columns i else default
  pf := openCore scheme n (OrderedOpening.query indices).coordinates (fun i => bind i (nonces i)) columns

theorem claim_value (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf)
    (i : Fin n) (inside : i ∈ (OrderedOpening.query indices).coordinates) :
    (claim scheme bind indices nonces columns).a i = columns i := if_pos inside

theorem decode_raw (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    OrderedOpening.decode bind indices (raw scheme bind indices nonces columns) =
      some (claim scheme bind indices nonces columns) := by
  have length : (raw scheme bind indices nonces columns).frontier.length =
      (Heap.frontierList n (OrderedOpening.query indices).coordinates).length := List.length_map ..
  unfold OrderedOpening.decode
  rw [dif_pos length]
  congr 1
  apply congrArg₂ (OpeningClaim.mk (OrderedOpening.query indices).coordinates)
  · funext i
    by_cases inside : i ∈ (OrderedOpening.query indices).coordinates
    · simp only [raw,dif_pos inside,if_pos inside]
      congr 1
      exact congrArg Subtype.val ((OrderedOpening.order indices).apply_symm_apply ⟨i,inside⟩)
    · simp only [dif_neg inside,if_neg inside]
  · apply congrArg₂ Opening.mk
    · funext i
      change bind i.val (nonces (indices ((OrderedOpening.order indices).symm i))) = bind i.val (nonces i.val)
      exact congrArg (fun j => bind i.val (nonces j))
        (congrArg Subtype.val ((OrderedOpening.order indices).apply_symm_apply i))
    · funext vertex
      change ((Heap.frontierList n (OrderedOpening.query indices).coordinates).map
          (commitLabels scheme n (fun i => bind i (nonces i)) columns))[(Heap.frontierList n
            (OrderedOpening.query indices).coordinates).idxOf vertex.val]'(by
              rw [List.length_map]
              exact List.idxOf_lt_length_of_mem (Heap.mem_frontierList.mpr vertex.property)) = _
      rw [List.getElem_map,List.getElem_idxOf]

omit [Inhabited Leaf] in
theorem checkValues_agree (scheme : Scheme Salt Leaf D Enc) (I : Finset (Fin n))
    (first second : Fin n → Leaf) (proof : Opening n I Salt D)
    (same : ∀ i ∈ I, first i = second i) (vertex : ℕ) :
    checkValues scheme n I first proof vertex = checkValues scheme n I second proof vertex := by
  conv_lhs => rw [checkValues]
  conv_rhs => rw [checkValues]
  split_ifs with leaf opened frontier frontier path
  · rw [same _ opened]
  · rfl
  · rfl
  · rfl
  · rw [checkValues_agree scheme I first second proof same (2*vertex),
      checkValues_agree scheme I first second proof same (2*vertex+1)]
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem claim_accepts (scheme : Scheme Salt Leaf D Enc) (bind : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (positive : 0 < t) (nonces : Fin n → Nonce) (columns : Fin n → Leaf) :
    Accepts scheme n (root scheme n (fun i => bind i (nonces i)) columns)
      (claim scheme bind indices nonces columns).I
      (claim scheme bind indices nonces columns).a (claim scheme bind indices nonces columns).pf := by
  have nonempty : (OrderedOpening.query indices).coordinates.Nonempty :=
    Finset.card_pos.mp (by simpa only [QuerySet.card_coordinates] using positive)
  refine ⟨nonempty,?_⟩
  change checkValues scheme n (OrderedOpening.query indices).coordinates
      (fun i => if i ∈ (OrderedOpening.query indices).coordinates then columns i else default)
      (openCore scheme n (OrderedOpening.query indices).coordinates (fun i => bind i (nonces i)) columns) 1 = _
  rw [checkValues_agree scheme _ _ columns _ (fun i inside => if_pos inside)]
  exact (mh_core_completeness scheme n (OrderedOpening.query indices).coordinates nonempty
    (fun i => bind i (nonces i)) columns).2

end LfzkV2.Current.ZeroKnowledge.CompleteOpening
