import LfzkV2.Current.ZeroKnowledge.MerkleRuntime
import Merkle.Hiding

/-! The backend's pair of participant columns and the runtime's typed tuple
are two presentations of the same committed data. Their actual hash inputs,
heap labels and complete commitment trace coincide. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MerkleRuntimeTransport
open Merkle Merkle.MH RecursivePolygero
open scoped Classical

section Inputs
variable {SaltA SaltB MessageA MessageB D EncA EncB : Type} [Inhabited D]
variable (first : Scheme SaltA MessageA D EncA) (second : Scheme SaltB MessageB D EncB)
variable (count : ℕ) (nonceA : Fin count → SaltA) (nonceB : Fin count → SaltB)
variable (messagesA : Fin count → MessageA) (messagesB : Fin count → MessageB)
variable (leaf : ∀ i, first.H (first.leafEnc (nonceA i,messagesA i)) = second.H (second.leafEnc (nonceB i,messagesB i)))
variable (node : ∀ children, first.H (first.nodeEnc children) = second.H (second.nodeEnc children))

include leaf node in
theorem commitLabels_of_inputs (vertex : ℕ) :
    commitLabels first count nonceA messagesA vertex = commitLabels second count nonceB messagesB vertex := by
  conv_lhs => rw [commitLabels]
  conv_rhs => rw [commitLabels]
  split_ifs with atLeaf internal
  · exact leaf _
  · rw [commitLabels_of_inputs (2*vertex),commitLabels_of_inputs (2*vertex+1)]
    exact node _
  · rfl
termination_by 2*count-vertex
decreasing_by all_goals omega

end Inputs

section Encodings
variable {SaltA SaltB MessageA MessageB D Enc : Type} [Inhabited D] [DecidableEq Enc]
variable (first : Codec SaltA MessageA D Enc) (second : Codec SaltB MessageB D Enc)
variable (count : ℕ) (nonceA : Fin count → SaltA) (nonceB : Fin count → SaltB)
variable (messagesA : Fin count → MessageA) (messagesB : Fin count → MessageB)

/-- Equal canonical leaf and node inputs preserve the complete execution,
including repeated queries. This symbolic step-count lemma keeps callers
from reducing a concrete commitment pass. -/
theorem pass_run_of_encodings (H : Enc → D)
    (leaf : ∀ i, first.leafEnc (nonceA i,messagesA i) = second.leafEnc (nonceB i,messagesB i))
    (node : ∀ children, first.nodeEnc children = second.nodeEnc children)
    (steps : ℕ) (values : ℕ → D) :
    (commitPass first count nonceA messagesA steps values).run H =
      (commitPass second count nonceB messagesB steps values).run H := by
  induction steps generalizing values with
  | zero => rfl
  | succ steps ih =>
      by_cases atLeaf : count ≤ steps+1 ∧ steps+1 < 2*count
      · simp only [commitPass,dif_pos atLeaf,RandomOracle.Tree.run_query,leaf]
        exact congrArg (fun rest => (rest.1,(_,_)::rest.2)) (ih _)
      · by_cases internal : 0 < steps+1 ∧ steps+1 < count
        · simp only [commitPass,dif_neg atLeaf,dif_pos internal,RandomOracle.Tree.run_query,node]
          exact congrArg (fun rest => (rest.1,(_,_)::rest.2)) (ih _)
        · simpa only [commitPass,dif_neg atLeaf,dif_neg internal,RandomOracle.Tree.run_weaken] using
            ih (Function.update values (steps+1) default)

end Encodings

section Pass
variable {SaltA SaltB MessageA MessageB D EncA EncB : Type} [Inhabited D] [DecidableEq EncA]
variable (first : Codec SaltA MessageA D EncA) (H : EncA → D)
variable (second : Scheme SaltB MessageB D EncB)
variable (count : ℕ) (nonceA : Fin count → SaltA) (nonceB : Fin count → SaltB)
variable (messagesA : Fin count → MessageA) (messagesB : Fin count → MessageB)

theorem pass_value_of_inputs
    (leaf : ∀ i, H (first.leafEnc (nonceA i,messagesA i)) = second.H (second.leafEnc (nonceB i,messagesB i)))
    (node : ∀ children, H (first.nodeEnc children) = second.H (second.nodeEnc children))
    (vertex : ℕ) (positive : 0 < vertex) :
    ((commitPass first count nonceA messagesA (2*count-1) (fun _ => default)).run H).1 vertex =
      commitLabels second count nonceB messagesB vertex := by
  have computed := Merkle.MH.commitPass_run first count nonceA messagesA H (2*count-1) (fun _ => default)
    (fun v beyond => (commitLabels_of_ge (S := first.withOracle H) count nonceA messagesA v (by omega)).symm)
    vertex positive
  exact computed.trans (commitLabels_of_inputs (first.withOracle H) second count nonceA nonceB messagesA messagesB leaf node vertex)

end Pass

theorem openingView_eq_of_labels {D Nonce : Type} (count : ℕ) (I : Finset (Fin count))
    (nonce : Fin count → Nonce) (first second : ℕ → D)
    (agree : ∀ vertex, 0 < vertex → first vertex = second vertex) :
    (⟨first 1,{ nonce := fun i => nonce i.val,frontierValue := fun vertex => first vertex.val }⟩ : OpeningView count I Nonce D) =
      ⟨second 1,{ nonce := fun i => nonce i.val,frontierValue := fun vertex => second vertex.val }⟩ := by
  apply congrArg₂ OpeningView.mk (agree 1 (by decide))
  apply congrArg₂ Opening.mk rfl
  funext vertex
  exact agree vertex.val (lt_trans (by decide : 0 < 1) (Heap.mem_frontier_iff.mp vertex.property).1)

section Root
variable {SaltA SaltB MessageA MessageB D EncA EncB : Type} [Inhabited D] [DecidableEq EncA]
variable (first : Codec SaltA MessageA D EncA) (H : EncA → D)
variable (second : Scheme SaltB MessageB D EncB)
variable (count : ℕ) (nonceA : Fin count → SaltA) (nonceB : Fin count → SaltB)
variable (messagesA : Fin count → MessageA) (messagesB : Fin count → MessageB)

theorem pass_root_of_inputs
    (leaf : ∀ i, H (first.leafEnc (nonceA i,messagesA i)) = second.H (second.leafEnc (nonceB i,messagesB i)))
    (node : ∀ children, H (first.nodeEnc children) = second.H (second.nodeEnc children)) :
    ((commitPass first count nonceA messagesA (2*count-1) (fun _ => default)).run H).1 1 =
      root second count nonceB messagesB :=
  pass_value_of_inputs first H second count nonceA nonceB messagesA messagesB leaf node 1 (by decide)

/-- Root and frontier are transported together; callers supply only the
canonical input equalities and never expose the internal heap traversal. -/
theorem pass_opening_of_inputs (I : Finset (Fin count))
    (leaf : ∀ i, H (first.leafEnc (nonceA i,messagesA i)) = second.H (second.leafEnc (nonceB i,messagesB i)))
    (node : ∀ children, H (first.nodeEnc children) = second.H (second.nodeEnc children)) :
    (let values := ((commitPass first count nonceA messagesA (2*count-1) (fun _ => default)).run H).1;
      (⟨values 1,{ nonce := fun i => nonceA i.val,frontierValue := fun vertex => values vertex.val }⟩ :
        OpeningView count I SaltA D)) =
      ⟨root second count nonceB messagesB,
        { nonce := fun i => nonceA i.val
          frontierValue := fun vertex => commitLabels second count nonceB messagesB vertex.val }⟩ :=
  openingView_eq_of_labels count I nonceA _ _
    (pass_value_of_inputs first H second count nonceA nonceB messagesA messagesB leaf node)

end Root

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)
variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (fits : n ≤ 2^64)
variable (H : Bytes → Digest) (nonce : Fin n → Fin n × Digest)
variable (columns : Fin n → MerkleCompiler.Leaf P.Carrier P.backend.nw 0 ×
  MerkleCompiler.Leaf R.Carrier R.backend.nw 0)

theorem commitLabels_eq (vertex : ℕ) :
    commitLabels ((MerkleRuntime.codec P R repr binary prime context fits).withOracle H) n nonce columns vertex =
      commitLabels ((MerkleWireCodec.codec P R repr binary prime context fits).withOracle H) n nonce
        (fun i => MerkleRuntime.tupleLeaf P R (columns i)) vertex :=
  commitLabels_of_inputs _ _ n nonce nonce columns
    (fun i => MerkleRuntime.tupleLeaf P R (columns i)) (fun _ => rfl) (fun _ => rfl) vertex

theorem root_eq :
    root ((MerkleRuntime.codec P R repr binary prime context fits).withOracle H) n nonce columns =
      root ((MerkleWireCodec.codec P R repr binary prime context fits).withOracle H) n nonce
        (fun i => MerkleRuntime.tupleLeaf P R (columns i)) :=
  commitLabels_eq P R repr binary prime context fits H nonce columns 1

theorem commitPass_run (count : ℕ) (values : ℕ → Digest) :
    (commitPass (MerkleRuntime.codec P R repr binary prime context fits) n nonce columns count values).run H =
      (commitPass (MerkleWireCodec.codec P R repr binary prime context fits) n nonce
        (fun i => MerkleRuntime.tupleLeaf P R (columns i)) count values).run H :=
  pass_run_of_encodings _ _ n nonce nonce columns
    (fun i => MerkleRuntime.tupleLeaf P R (columns i)) H (fun _ => rfl) (fun _ => rfl) count values

end LfzkV2.Current.ZeroKnowledge.MerkleRuntimeTransport
