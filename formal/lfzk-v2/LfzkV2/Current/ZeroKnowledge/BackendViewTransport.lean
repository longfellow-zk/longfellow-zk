import LfzkV2.Current.ZeroKnowledge.BackendCompiled

/-! Transport a backend view through an already computed Merkle opening.
The heap pass stays opaque: these equalities do not evaluate its concrete
number of query steps while comparing the two observer callbacks. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendViewTransport
open Merkle Merkle.MH Merkle.RandomOracle LigeroFamily
open scoped Classical
variable {B N : Type} [Field B] [Field N]
variable {r w n bw nw s : ℕ}
variable {Nonce D Enc Front Request Observed : Type}
variable [DecidableEq Enc] [Inhabited D]
variable (codec : Codec (Fin n × Nonce) (BackendCompiled.Leaf (B := B) (N := N) (bw := bw) (nw := nw)) D Enc)
variable (queries : ℕ) (Q : QuerySet n r)
variable (observer : Request → (Front × BackendCompiled.Responses (B := B) (N := N) (r := r) (w := w) (s := s)) →
  ({i : Fin n // i ∈ Q.coordinates} → BackendCompiled.Leaf (B := B) (N := N) (bw := bw) (nw := nw)) →
  BackendCompiled.Labels n D → OpeningView n Q.coordinates Nonce D → Tree Enc D Observed queries)

theorem runView_of_opening (request : Request)
    (columns : Fin n → BackendCompiled.Leaf (B := B) (N := N) (bw := bw) (nw := nw))
    (publicView : Front × BackendCompiled.Responses (B := B) (N := N) (r := r) (w := w) (s := s))
    (nonces : Fin n → Nonce) (H : Enc → D) (labels : BackendCompiled.Labels n D)
    (opened : OpeningView n Q.coordinates Nonce D)
    (matching :
      (let values := ((commitPass (MerkleSimulation.nonceCodec codec) n nonces
        (fun i => (i,columns i)) (2*n-1) (fun _ => default)).run H).1
       (⟨values 1,{ nonce := fun i => nonces i.val,frontierValue := fun vertex => values vertex.val }⟩ :
         OpeningView n Q.coordinates Nonce D)) = opened) :
    BackendCompiled.runView codec queries Q id observer request columns publicView nonces H labels =
      ((observer request publicView (fun i => columns i.val) labels opened).run H).1 := by
  exact congrArg
    (fun opening => ((observer request publicView (fun i => columns i.val) labels opening).run H).1) matching

theorem actualLabels_last {Salt Message : Type} (codec : Codec Salt Message D Enc)
    (positive : 0 < n) (nonces : Fin n → Salt) (messages : Fin n → Message) (H : Enc → D) :
    MerklePreparation.actualLabels codec n nonces messages H ⟨2*n-2,by omega⟩ =
      ((commitPass codec n nonces messages (2*n-1) (fun _ => default)).run H).1 1 := by
  unfold MerklePreparation.actualLabels
  change ((commitPass codec n nonces messages (2*n-1) (fun _ => default)).run H).1 (2*n-1-(2*n-2)) = _
  rw [show 2*n-1-(2*n-2) = 1 by omega]

end LfzkV2.Current.ZeroKnowledge.BackendViewTransport
