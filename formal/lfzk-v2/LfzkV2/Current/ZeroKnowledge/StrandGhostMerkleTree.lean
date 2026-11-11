import Merkle.Indexed.Codec
import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleSwap

/-! A ghost commitment contains independent leaf digests and ordinary
indexed internal hashes. Only opened leaf preimages need be installed.
The equalities below hold even when digest outputs collide: they compare
actual oracle evaluations, not an array of assumed distinct tree labels. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Tree
open Merkle Merkle.Indexed
open scoped Classical

variable {Nonce Message Digest Raw : Type} {n : ℕ}
variable (codec : Codec (Fin n × Nonce) Message Digest Raw)
variable (dec : RoleDecoders codec)

def addresses (nonces : Fin n → Nonce) (columns : Fin n → Message) : Fin n ↪ Raw where
  toFun index := codec.leafEnc ((index,nonces index),columns index)
  inj' _ _ same := congrArg (fun value : (Fin n × Nonce) × Message => value.1.1)
    (dec.inj.leaf same)

def openedAddresses (I : Finset (Fin n)) (nonces : I → Nonce) (columns : I → Message) : I ↪ Raw where
  toFun index := codec.leafEnc ((index.val,nonces index),columns index)
  inj' _ _ same := Subtype.ext (congrArg (fun value : (Fin n × Nonce) × Message => value.1.1)
    (dec.inj.leaf same))

/-- The simulator's only programmed addresses use disclosed columns and
their nonces. There is no unopened-column or hidden-nonce argument. -/
def installOpened (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : I → Nonce) (columns : I → Message) (leaves : Fin n → Digest) : Raw → Digest :=
  Swap.replace (openedAddresses codec dec I nonces columns) H (fun index => leaves index.val)

def installAll (H : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest) : Raw → Digest :=
  Swap.replace (addresses codec dec nonces columns) H leaves

theorem installOpened_empty (H : Raw → Digest)
    (nonces : (∅ : Finset (Fin n)) → Nonce) (columns : (∅ : Finset (Fin n)) → Message)
    (leaves : Fin n → Digest) : installOpened codec dec H ∅ nonces columns leaves = H := by
  funext raw
  apply Swap.replace_off
  intro index
  exact False.elim (Finset.notMem_empty index.val index.property)

theorem installOpened_leaf (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : I → Nonce) (columns : I → Message) (leaves : Fin n → Digest) (index : I) :
    installOpened codec dec H I nonces columns leaves
      (codec.leafEnc ((index.val,nonces index),columns index)) = leaves index.val :=
  Swap.replace_at _ _ _ index

theorem installAll_leaf (H : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest) (index : Fin n) :
    installAll codec dec H nonces columns leaves
      (codec.leafEnc ((index,nonces index),columns index)) = leaves index :=
  Swap.replace_at _ _ _ index

variable (separated : ∀ index children salt message,
  codec.nodeEnc index children ≠ codec.leafEnc (salt,message))

include separated in
theorem installAll_node (H : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest) (index : ℕ) (children : Digest × Digest) :
    installAll codec dec H nonces columns leaves (codec.nodeEnc index children) =
      H (codec.nodeEnc index children) :=
  Swap.replace_off _ _ _ _ (fun _ => separated _ _ _ _)

include separated in
theorem installOpened_node (H : Raw → Digest) (I : Finset (Fin n))
    (nonces : I → Nonce) (columns : I → Message) (leaves : Fin n → Digest)
    (index : ℕ) (children : Digest × Digest) :
    installOpened codec dec H I nonces columns leaves (codec.nodeEnc index children) =
      H (codec.nodeEnc index children) :=
  Swap.replace_off _ _ _ _ (fun _ => separated _ _ _ _)

variable [Inhabited Digest]

/-- All internal nodes are memoized calls to the supplied ordinary oracle,
at their actual heap indices. Their answers are never independently chosen. -/
def labels (H : Raw → Digest) (leaves : Fin n → Digest) (vertex : ℕ) : Digest :=
  if leaf : n ≤ vertex ∧ vertex < 2*n then leaves ⟨vertex-n,by omega⟩
  else if 0 < vertex ∧ vertex < n then
    H (codec.nodeEnc vertex (labels H leaves (2*vertex),labels H leaves (2*vertex+1)))
  else default
termination_by 2*n-vertex
decreasing_by all_goals omega

/-- Only the opened nonces are part of authentication. Frontier labels are
computed from the ghost tree, independently of every hidden nonce. -/
def opening (H : Raw → Digest) (leaves : Fin n → Digest) (I : Finset (Fin n))
    (nonces : I → Nonce) : Opening n I (Fin n × Nonce) Digest where
  nonce index := (index.val,nonces index)
  frontierValue vertex := labels codec H leaves vertex.val

theorem labels_congr (first second : Raw → Digest)
    (same : ∀ index, index < n → ∀ children, first (codec.nodeEnc index children) = second (codec.nodeEnc index children))
    (leaves : Fin n → Digest) (vertex : ℕ) : labels codec first leaves vertex = labels codec second leaves vertex := by
  conv_lhs => rw [labels]
  conv_rhs => rw [labels]
  split_ifs with leaf internal
  · rfl
  · rw [labels_congr first second same leaves (2*vertex),labels_congr first second same leaves (2*vertex+1)]
    exact same vertex internal.2 _
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem opening_congr (first second : Raw → Digest)
    (same : ∀ index, index < n → ∀ children, first (codec.nodeEnc index children) = second (codec.nodeEnc index children))
    (leaves : Fin n → Digest) (I : Finset (Fin n)) (nonces : I → Nonce) :
    opening codec first leaves I nonces = opening codec second leaves I nonces := by
  apply congrArg₂ Merkle.MH.Opening.mk rfl
  funext vertex
  exact labels_congr codec first second same leaves vertex.val

theorem commit_eq_labels (H full : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest)
    (leafAnswers : ∀ index, full (codec.leafEnc ((index,nonces index),columns index)) = leaves index)
    (nodeAnswers : ∀ index children, full (codec.nodeEnc index children) = H (codec.nodeEnc index children))
    (vertex : ℕ) :
    commitLabels (codec.withOracle full) n (fun index => (index,nonces index)) columns vertex =
      labels codec H leaves vertex := by
  refine WellFounded.induction (measure (fun vertex : ℕ => 2*n-vertex)).wf vertex
    (C := fun current =>
      commitLabels (codec.withOracle full) n (fun index => (index,nonces index)) columns current =
        labels codec H leaves current) ?_
  intro current ih
  rw [commitLabels,labels]
  split_ifs with leaf node
  · exact leafAnswers ⟨current-n,by omega⟩
  · change full (codec.nodeEnc current
        (commitLabels (codec.withOracle full) n (fun index => (index,nonces index)) columns (2*current),
          commitLabels (codec.withOracle full) n (fun index => (index,nonces index)) columns (2*current+1))) = _
    rw [nodeAnswers,ih (2*current) (by change 2*n-2*current < 2*n-current; omega),
      ih (2*current+1) (by change 2*n-(2*current+1) < 2*n-current; omega)]
  · rfl

include separated in
theorem installAll_commit (H : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest) (vertex : ℕ) :
    commitLabels (codec.withOracle (installAll codec dec H nonces columns leaves)) n
        (fun index => (index,nonces index)) columns vertex = labels codec H leaves vertex :=
  commit_eq_labels codec H _ nonces columns leaves (installAll_leaf codec dec H nonces columns leaves)
    (installAll_node codec dec separated H nonces columns leaves) vertex

include separated in
theorem installAll_opening (H : Raw → Digest) (nonces : Fin n → Nonce)
    (columns : Fin n → Message) (leaves : Fin n → Digest) (I : Finset (Fin n)) :
    openCore (codec.withOracle (installAll codec dec H nonces columns leaves)) n I
        (fun index => (index,nonces index)) columns =
      opening codec H leaves I (fun index => nonces index.val) := by
  apply congrArg₂ Merkle.MH.Opening.mk
  · rfl
  · funext vertex
    exact installAll_commit codec dec separated H nonces columns leaves vertex.val

end LfzkV2.Current.ZeroKnowledge.StrandGhostMerkle.Tree
