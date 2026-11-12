import LfzkV2.Current.MerkleReplay
import LfzkV2.Current.ReplayPrefix
import LfzkV2.Current.BackendPositions

/-! The wire opening stores cells and salts in sampled order, with the
frontier in decreasing heap order. Query positions are reconstructed from
the opening boundary answer; they are not extra serialized proof data. -/
noncomputable section
namespace LfzkV2.Current.OrderedOpening
open Merkle Merkle.MH LigeroFamily
open scoped Classical

variable {n t : ℕ} {Salt Nonce Leaf D : Type}

/-- The set underlying the verifier's ordered sample without replacement. -/
def query (indices : Fin t ↪ Fin n) : QuerySet n t :=
  ⟨Finset.univ.image indices, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, by simp [Finset.card_image_of_injective _ indices.injective]⟩⟩

/-- Reindexing preserves the sampled order even though the algebraic backend
uses a set. All fields and nonce bytes use this same reindexing. -/
def order (indices : Fin t ↪ Fin n) : Fin t ≃ ↥(query indices).coordinates :=
  Equiv.ofBijective (fun i => ⟨indices i, by simp [query, QuerySet.coordinates]⟩)
    ⟨by intro i j h; exact indices.injective (congrArg Subtype.val h), by
      rintro ⟨j,hj⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
      exact ⟨i,Subtype.ext hi⟩⟩

@[simp] theorem order_val (indices : Fin t ↪ Fin n) (i : Fin t) :
    ((order indices) i).val = indices i := rfl

/-- The authentication payload before query-dependent heap addresses are
reconstructed. A caller supplies the fixed-width tuple leaf decoder. -/
structure Raw (t : ℕ) (Nonce Leaf D : Type) where
  values : Fin t → Leaf
  nonce : Fin t → Nonce
  frontier : List D

variable [Inhabited Leaf]

/-- Reconstruct the exact indexed claim checked by the mathematical Merkle
verifier. Position-dependent salt framing adds the public column index here,
not on the wire. A wrong frontier length is rejected before indexing any bytes. -/
def decode (bindSalt : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (raw : Raw t Nonce Leaf D) :
    Option (OpeningClaim n Salt Leaf D) :=
  if h : raw.frontier.length = (Heap.frontierList n (query indices).coordinates).length then
    some {
      I := (query indices).coordinates
      a := fun j => if hj : j ∈ (query indices).coordinates then
        raw.values ((order indices).symm ⟨j,hj⟩) else default
      pf := {
        nonce := fun j => bindSalt j.val (raw.nonce ((order indices).symm j))
        frontierValue := fun v =>
          raw.frontier[(Heap.frontierList n (query indices).coordinates).idxOf v.val]'(by
            rw [h]
            exact List.idxOf_lt_length_of_mem (Heap.mem_frontierList.mpr v.property)) } }
  else none

/-- Decoding fixes the opened set to the query derived from the transcript. -/
theorem decode_indices (bindSalt : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (raw : Raw t Nonce Leaf D)
    (claim : OpeningClaim n Salt Leaf D) (h : decode bindSalt indices raw = some claim) :
    claim.I = (query indices).coordinates := by
  unfold decode at h
  split_ifs at h with hf
  · exact congrArg OpeningClaim.I (Option.some.inj h).symm

/-- Each queried position receives exactly its corresponding tuple column. -/
theorem decode_values (bindSalt : Fin n → Nonce → Salt)
    (indices : Fin t ↪ Fin n) (raw : Raw t Nonce Leaf D)
    (claim : OpeningClaim n Salt Leaf D) (h : decode bindSalt indices raw = some claim) (i : Fin t) :
    claim.a (indices i) = raw.values i := by
  unfold decode at h
  split_ifs at h with hf
  · cases Option.some.inj h
    simp only [dif_pos (show indices i ∈ (query indices).coordinates from by
      simp [query, QuerySet.coordinates])]
    congr 1
    apply (order indices).injective
    exact (order indices).apply_symm_apply _

section Replay
variable {g : Geometry} {F : Fields} {Advice Auth Context Block C : Type}

/-- Read the shared opening answer from the verifier cache. No transcript
history is needed. The fallback only totalizes incomplete caches; a completed
replay always contains this answer. -/
def openingAnswer {count : ℕ} (fallback : C) (answers : Replay.VerifierState C count) : C :=
  if h : g.openingIndex.val < count then answers ⟨g.openingIndex.val,h⟩ else fallback

/-- The indexed claim is analysis data reconstructed after the ordinary
rounds. The original proof and its final-seal body are never extended. -/
def read (bindSalt : Fin n → Nonce → Salt)
    (sample : C → (Fin t ↪ Fin n)) (fallback : C)
    (rawOf : Replay.Output g F Advice Auth → Raw t Nonce Leaf D)
    (annotated : MerkleReplay.Annotated g F Advice Auth Context Block C) :
    Option (OpeningClaim n Salt Leaf D) :=
  decode bindSalt (sample (openingAnswer (g := g) fallback annotated.2.answers)) (rawOf annotated.1)

variable (e : Replay.Encoding g F Advice Auth Context Block C) (initialLink : Digest)
  (proof : Replay.Output g F Advice Auth)
  (H : Replay.Point g F Advice Auth Context Block → Digest × C)

/-- Reconstruction uses exactly the one shared opening answer. -/
theorem openingAnswer_replay (fallback : C) :
    openingAnswer (g := g) fallback ((e.chain initialLink).replay proof H g.roles.length).answers =
      (H ((e.chain initialLink).point proof H g.openingIndex.val)).2 := by
  have hr := (e.chain initialLink).point_rank proof H (Nat.le_refl g.roles.length)
  change ((e.chain initialLink).replay proof H g.roles.length).point.rank = g.roles.length at hr
  have hlt : g.openingIndex.val <
      ((e.chain initialLink).replay proof H g.roles.length).point.rank := by
    rw [hr]
    exact g.openingIndex.isLt
  unfold openingAnswer
  rw [dif_pos hlt]
  exact e.replay_answer initialLink proof H g.roles.length (by rfl) ⟨_,hlt⟩

theorem read_replay (bindSalt : Fin n → Nonce → Salt)
    (sample : C → (Fin t ↪ Fin n)) (fallback : C)
    (rawOf : Replay.Output g F Advice Auth → Raw t Nonce Leaf D) :
    read bindSalt sample fallback rawOf (proof,(e.chain initialLink).replay proof H g.roles.length) =
      decode bindSalt (sample (H ((e.chain initialLink).point proof H g.openingIndex.val)).2) (rawOf proof) := by
  simp only [read, openingAnswer_replay]

theorem read_indices_replay (bindSalt : Fin n → Nonce → Salt)
    (sample : C → (Fin t ↪ Fin n)) (fallback : C)
    (rawOf : Replay.Output g F Advice Auth → Raw t Nonce Leaf D)
    (claim : OpeningClaim n Salt Leaf D)
    (h : read bindSalt sample fallback rawOf
      (proof,(e.chain initialLink).replay proof H g.roles.length) = some claim) :
    claim.I = (query (sample (H ((e.chain initialLink).point proof H g.openingIndex.val)).2)).coordinates := by
  rw [read_replay] at h
  exact decode_indices _ _ _ _ h

end Replay
end LfzkV2.Current.OrderedOpening
