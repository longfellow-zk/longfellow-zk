import TranscriptV2.StrandTranscript

/-! The current protocol uses only numbered continuation nodes.
Its relevant parent claims are therefore singletons. Multi-
parent auxiliary inputs remain legal SHA queries, but are not accepted round
nodes. Their hash answers are still present in the shared query table. -/
namespace TranscriptV2.Strand
open Framing Finset Merkle.RandomOracle
open scoped Classical

noncomputable def linearParents : Input → Finset Digest
  | .prf _ parent _ => {parent}
  | .node _ [parent] _ => {parent}
  | _ => ∅

noncomputable def linearClaims (raw : Bytes) : Finset Digest :=
  match Input.decode raw with
  | some input => linearParents input
  | none => ∅

@[simp] theorem linearClaims_prf (id : Word) (parent : Digest) (counter : Word) :
    linearClaims (Input.prf id parent counter).encode = {parent} := by
  simp only [linearClaims,Input.decode_encode (.prf id parent counter) trivial,linearParents]

@[simp] theorem linearClaims_continuation (id : Word) (parent : Digest) (message : Bytes) :
    linearClaims ((continuation id parent).write message).input.encode = {parent} := by
  rw [linearClaims,Input.decode_encode _ (((continuation id parent).write message).valid)]
  rfl

@[simp] theorem digest_card : Fintype.card Digest = 2^256 := by
  simp only [Digest,Byte,Fintype.card_fun,Fintype.card_fin]
  norm_num

end TranscriptV2.Strand
