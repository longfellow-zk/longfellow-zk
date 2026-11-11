import LfzkV2.Current.ZeroKnowledge.StrandGhostMerkleTree
import LfzkV2.Current.OracleWindow

/-! Raw query support for the indexed commitment and its ghost-label tree.
Internal positions range over the actual heap; the support is fixed before
sampling any oracle, nonce, message, or response-selected opening. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandMerkleWindow
open Merkle Merkle.Indexed
open scoped Classical

variable {Salt Message Digest Raw : Type} [Fintype Salt] [Fintype Message] [Fintype Digest] [DecidableEq Raw]
variable (codec : Codec Salt Message Digest Raw) (n : ℕ)

def window : Finset Raw :=
  (Finset.univ.image codec.leafEnc) ∪
    (Finset.univ.image fun data : Fin n × (Digest × Digest) => codec.nodeEnc data.1.val data.2)

theorem leaf_mem (value : Salt × Message) : codec.leafEnc value ∈ window codec n :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨value,Finset.mem_univ _,rfl⟩)

theorem node_mem (index : ℕ) (within : index < n) (children : Digest × Digest) :
    codec.nodeEnc index children ∈ window codec n := by
  unfold window
  apply Finset.mem_union_right
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  exact ⟨(⟨index,within⟩,children),rfl⟩

variable [Inhabited Digest]

theorem commitLabels_congr (first second : Raw → Digest)
    (same : ∀ raw ∈ window codec n, first raw = second raw)
    (nonces : Fin n → Salt) (messages : Fin n → Message) (vertex : ℕ) :
    commitLabels (codec.withOracle first) n nonces messages vertex =
      commitLabels (codec.withOracle second) n nonces messages vertex := by
  conv_lhs => rw [commitLabels]
  conv_rhs => rw [commitLabels]
  split_ifs with leaf internal
  · exact same _ (leaf_mem codec n _)
  · rw [commitLabels_congr first second same nonces messages (2*vertex),
      commitLabels_congr first second same nonces messages (2*vertex+1)]
    exact same _ (node_mem codec n vertex internal.2 _)
  · rfl
termination_by 2*n-vertex
decreasing_by all_goals omega

theorem openCore_congr (first second : Raw → Digest)
    (same : ∀ raw ∈ window codec n, first raw = second raw)
    (I : Finset (Fin n)) (nonces : Fin n → Salt) (messages : Fin n → Message) :
    openCore (codec.withOracle first) n I nonces messages =
      openCore (codec.withOracle second) n I nonces messages := by
  apply congrArg₂ Merkle.MH.Opening.mk rfl
  funext vertex
  exact commitLabels_congr codec n first second same nonces messages vertex.val

end LfzkV2.Current.ZeroKnowledge.StrandMerkleWindow
