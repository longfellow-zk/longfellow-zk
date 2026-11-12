import Merkle.Commit

/-! A public column index can be included in a generic Merkle leaf message.
Only its nonce is random.  For the hiding theorem we therefore
regard the column index as part of the message, rather than silently treating
the pair `(index,nonce)` as uniform randomness.  This is a change of analysis
coordinates: every encoded byte, heap label and opening check is unchanged. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleSimulation

open Merkle Merkle.MH Finset
open scoped Classical

section Reindex
variable {Index Nonce Leaf D Enc : Type}
variable (codec : Codec (Index × Nonce) Leaf D Enc)

def shuffle : (Nonce × (Index × Leaf)) ≃ ((Index × Nonce) × Leaf) where
  toFun x := ((x.2.1,x.1),x.2.2)
  invFun x := (x.1.2,(x.1.1,x.2))
  left_inv _ := rfl
  right_inv _ := rfl

def nonceCodec : Codec Nonce (Index × Leaf) D Enc where
  leafEnc x := codec.leafEnc (shuffle x)
  nodeEnc := codec.nodeEnc

theorem nonceCodec_inj (injective : codec.Inj) : (nonceCodec codec).Inj :=
  ⟨injective.leaf.comp shuffle.injective,injective.node⟩

@[simp] theorem nonceCodec_leaf (index : Index) (nonce : Nonce) (leaf : Leaf) :
    (nonceCodec codec).leafEnc (nonce,(index,leaf)) = codec.leafEnc ((index,nonce),leaf) := rfl

@[simp] theorem nonceCodec_node (children : D × D) :
    (nonceCodec codec).nodeEnc children = codec.nodeEnc children := rfl

variable [Inhabited D]

/-- Fixed public coordinates never contribute entropy to the hiding bound. -/
theorem commit_labels (H : Enc → D) (n : ℕ) (index : Fin n → Index)
    (nonce : Fin n → Nonce) (message : Fin n → Leaf) (vertex : ℕ) :
    commitLabels ((nonceCodec codec).withOracle H) n nonce
        (fun i => (index i,message i)) vertex =
      commitLabels (codec.withOracle H) n (fun i => (index i,nonce i)) message vertex := by
  conv_lhs => rw [commitLabels]
  conv_rhs => rw [commitLabels]
  split_ifs with leaf internal
  · rfl
  · change H (codec.nodeEnc (_, _)) = H (codec.nodeEnc (_, _))
    rw [commit_labels H n index nonce message (2*vertex),
      commit_labels H n index nonce message (2*vertex+1)]
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem root_eq (H : Enc → D) (n : ℕ) (index : Fin n → Index)
    (nonce : Fin n → Nonce) (message : Fin n → Leaf) :
    root ((nonceCodec codec).withOracle H) n nonce (fun i => (index i,message i)) =
      root (codec.withOracle H) n (fun i => (index i,nonce i)) message :=
  commit_labels codec H n index nonce message 1

def indexedOpening {n : ℕ} {I : Finset (Fin n)} (index : Fin n → Index)
    (proof : Opening n I Nonce D) : Opening n I (Index × Nonce) D where
  nonce i := (index i.val,proof.nonce i)
  frontierValue := proof.frontierValue

theorem check_values (H : Enc → D) (n : ℕ) (I : Finset (Fin n))
    (index : Fin n → Index) (message : Fin n → Leaf)
    (proof : Opening n I Nonce D) (vertex : ℕ) :
    checkValues ((nonceCodec codec).withOracle H) n I (fun i => (index i,message i)) proof vertex =
      checkValues (codec.withOracle H) n I message (indexedOpening index proof) vertex := by
  conv_lhs => rw [checkValues]
  conv_rhs => rw [checkValues]
  split_ifs with leaf opened frontier frontier path
  · rfl
  · rfl
  · rfl
  · rfl
  · change H (codec.nodeEnc (_, _)) = H (codec.nodeEnc (_, _))
    rw [check_values H n I index message proof (2*vertex),
      check_values H n I index message proof (2*vertex+1)]
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem accepts_iff (H : Enc → D) (n : ℕ) (I : Finset (Fin n))
    (index : Fin n → Index) (message : Fin n → Leaf) (digest : D)
    (proof : Opening n I Nonce D) :
    Accepts ((nonceCodec codec).withOracle H) n digest I
        (fun i => (index i,message i)) proof ↔
      Accepts (codec.withOracle H) n digest I message (indexedOpening index proof) := by
  simp only [Accepts,check_values]

end Reindex

end LfzkV2.Current.ZeroKnowledge.MerkleSimulation
