import Lfzk.NizkDeployedHash

/-!
# The deployed Ligero response and its Fiat--Shamir input

The verifier writes four fixed-length field slices, in order, after drawing
the Ligero linear-combination challenge and before drawing the column query.
Openings and Merkle paths come after that query.  The transcript's random
bytes are never written back into its hash accumulator.  Consequently the
query input contains the complete transmitted response and the preceding
*messages*, but not the raw linear-combination challenge.

This module makes those two facts explicit at the message-prefix interface.
It models the four arrays transmitted by `LigeroProof`, including the two
parts of the quadratic response; the zero middle part is reconstructed by
the verifier and is not transmitted.  Field-element serialization is a
parameter: injectivity of its fixed-width byte representation is the precise
byte-level obligation for an implementation instantiation.  SHA-256/PRF
idealization remains the separate assumption of `NizkDeployedHash`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroTranscriptInputs

open Lfzk.NizkDeployedHash

/-- The four response slices absorbed before `gen_idx`.  Their lengths are
the verifier's `block`, `dblock`, `r`, and `dblock - block` checks. -/
structure ResponsePayload (F : Type*) (block dblock r : ℕ) where
  yLdt : Fin block → F
  yDot : Fin dblock → F
  yQuad0 : Fin r → F
  yQuad2 : Fin (dblock - block) → F
  deriving Fintype, DecidableEq

namespace ResponsePayload

variable {F Byte : Type*} {block dblock r width : ℕ}

/-- The four ordered arrays of fixed-width serialized field elements.  The
runtime adds an array tag and length before each array.  As the lengths are
fixed here, the tags and lengths carry no response-dependent data. -/
def wireFields (encode : F → Fin width → Byte)
    (p : ResponsePayload F block dblock r) :
    (Fin block → Fin width → Byte) ×
      (Fin dblock → Fin width → Byte) ×
      (Fin r → Fin width → Byte) ×
      (Fin (dblock - block) → Fin width → Byte) :=
  (encode ∘ p.yLdt, encode ∘ p.yDot,
    encode ∘ p.yQuad0, encode ∘ p.yQuad2)

/-- Canonical fixed-width field serialization distinguishes complete
transmitted responses. -/
theorem wireFields_injective (encode : F → Fin width → Byte)
    (hencode : Function.Injective encode) :
    Function.Injective (wireFields (block := block) (dblock := dblock)
      (r := r) encode) := by
  intro p q h
  rcases p with ⟨pl, pd, pq0, pq2⟩
  rcases q with ⟨ql, qd, qq0, qq2⟩
  dsimp [wireFields] at h
  have hld := congrArg Prod.fst h
  have hdot := congrArg (fun x => x.2.1) h
  have hq0 := congrArg (fun x => x.2.2.1) h
  have hq2 := congrArg (fun x => x.2.2.2) h
  have hl : pl = ql := by
    funext i
    apply hencode
    exact congrFun hld i
  have hd : pd = qd := by
    funext i
    apply hencode
    exact congrFun hdot i
  have h0 : pq0 = qq0 := by
    funext i
    apply hencode
    exact congrFun hq0 i
  have h2 : pq2 = qq2 := by
    funext i
    apply hencode
    exact congrFun hq2 i
  simp [hl, hd, h0, h2]

/-- A concrete decoder into the evaluation-row response used by the IOP
proof must be injective before one can replace a sum over transmitted
responses by that proof's response-mass sum.  This lemma records the exact
bridge, without silently assuming it for an arbitrary `Msg → Response`. -/
theorem mass_le_of_decode_injective [Fintype F]
    {FormalResponse : Type} [Fintype FormalResponse]
    [DecidableEq FormalResponse]
    (decode : ResponsePayload F block dblock r → FormalResponse)
    (hdecode : Function.Injective decode)
    (cost : FormalResponse → ℚ)
    (hcost : ∀ response, 0 ≤ cost response) :
    ∑ payload : ResponsePayload F block dblock r, cost (decode payload) ≤
      ∑ response : FormalResponse, cost response := by
  classical
  let image := (Finset.univ : Finset (ResponsePayload F block dblock r)).image decode
  calc
    ∑ payload : ResponsePayload F block dblock r, cost (decode payload) =
        ∑ response ∈ image, cost response := by
          exact (Finset.sum_image (fun _ _ _ _ h => hdecode h)).symm
    _ ≤ ∑ response : FormalResponse, cost response := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ image)
      intro response _ _
      exact hcost response

end ResponsePayload

section Prefix

variable {Ctx Other F : Type} {nl block dblock r : ℕ} {w : ℕ → ℕ}
variable [Inhabited Other]

abbrev Message := Other ⊕ ResponsePayload F block dblock r

instance : Inhabited (Message (Other := Other) (F := F)
    (block := block) (dblock := dblock) (r := r)) :=
  ⟨Sum.inl default⟩

private abbrev challengeSlot (nl : ℕ) (w : ℕ → ℕ) : ℕ :=
  Rounds.Role.layerBase w nl + 1

private abbrev querySlot (nl : ℕ) (w : ℕ → ℕ) : ℕ :=
  Rounds.Role.layerBase w nl + 2

/-- Replace only the message immediately before the query challenge with
the transmitted four-slice response.  No verifier challenge is an argument. -/
def withResponse (msgs : ℕ → Message (Other := Other) (F := F)
    (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r) :=
  fun i => if i = querySlot nl w then Sum.inr response else msgs i

omit [Inhabited Other] in
/-- The typed schedule always places its transmitted response immediately
before the query challenge. -/
theorem withResponse_querySlot
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    withResponse (nl := nl) (w := w) msgs response
      (Rounds.Role.layerBase w nl + 2) = Sum.inr response := by
  simp [withResponse, querySlot]

/-- Hash input for the linear-combination challenge. -/
noncomputable def parentPoint (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) :
    MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w :=
  msgPoint ctx (fun _ => msgs) () (challengeSlot nl w)

/-- Hash input for `gen_idx`: the same message prefix extended with the
complete response.  Its type and definition contain no raw challenge. -/
noncomputable def childPoint (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w :=
  msgPoint ctx (fun _ => withResponse (nl := nl) (w := w) msgs response) ()
    (querySlot nl w)

/-- At a fixed message prefix, different complete transmitted responses give
different query hash inputs. -/
theorem childPoint_injective (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) :
    Function.Injective (childPoint (nl := nl) (w := w) ctx msgs) := by
  intro p q h
  have hslot : querySlot nl w < Rounds.Role.length nl w := by
    simp only [querySlot, Rounds.Role.length]
    omega
  have hmsg := congrArg
    (fun pt : MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w =>
      pt.msgFn (querySlot nl w)) h
  rw [childPoint, msgFn_msgPoint ctx _ () hslot (le_refl _),
    childPoint, msgFn_msgPoint ctx _ () hslot (le_refl _)] at hmsg
  simpa [withResponse] using hmsg

/-- When the message at the query slot is the four-slice response, the
ordinary deployed verifier point is exactly `childPoint`.  This is the
adapter from the existing `msgPoint` interface to the typed response input. -/
theorem childPoint_eq_msgPoint (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r)
    (hresponse : msgs (querySlot nl w) = Sum.inr response) :
    childPoint (nl := nl) (w := w) ctx msgs response =
      msgPoint ctx (fun _ => msgs) () (querySlot nl w) := by
  have hsame : withResponse (nl := nl) (w := w) msgs response = msgs := by
    funext i
    by_cases hi : i = querySlot nl w
    · subst i
      simpa [withResponse] using hresponse.symm
    · simp [withResponse, hi]
  simp only [childPoint, hsame]

/-- Changing the response leaves the parent challenge input unchanged. -/
theorem parentPoint_withResponse (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    parentPoint (nl := nl) (w := w) ctx
      (withResponse (nl := nl) (w := w) msgs response) =
      parentPoint (nl := nl) (w := w) ctx msgs := by
  unfold parentPoint msgPoint
  congr 1
  funext i
  simp only [padMsgs]
  split_ifs with hi
  · simp only [withResponse]
    have hne : i.val ≠ querySlot nl w := by
      simp only [challengeSlot] at hi
      simp only [querySlot]
      omega
    simp [hne]
  · rfl

/-- The parent's input is literally the query input's earlier-message
ancestor.  This remains true even when the child was queried first. -/
theorem parent_eq_child_ancestor (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    (mpoints (Ctx := Ctx) (Msg := Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) (nl := nl) (w := w)).anc
      (childPoint (nl := nl) (w := w) ctx msgs response)
      (challengeSlot nl w) =
        parentPoint (nl := nl) (w := w) ctx msgs := by
  have hlt : challengeSlot nl w < querySlot nl w := by
    simp only [challengeSlot, querySlot]
    omega
  have hquery : querySlot nl w < Rounds.Role.length nl w := by
    simp only [querySlot, Rounds.Role.length]
    omega
  rw [childPoint, anc_msgPoint ctx _ () hlt hquery]
  exact parentPoint_withResponse ctx msgs response

/-- Parent and child are distinct coordinates of the prefix-only oracle. -/
theorem parent_ne_child (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    parentPoint (nl := nl) (w := w) ctx msgs ≠
      childPoint (nl := nl) (w := w) ctx msgs response := by
  rw [← parent_eq_child_ancestor ctx msgs response]
  apply (mpoints (Ctx := Ctx) (Msg := Message (Other := Other) (F := F)
    (block := block) (dblock := dblock) (r := r)) (nl := nl) (w := w)).anc_ne
  have hquery : querySlot nl w < Rounds.Role.length nl w := by
    simp only [querySlot, Rounds.Role.length]
    omega
  change challengeSlot nl w <
    (mpoints (Ctx := Ctx) (Msg := Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) (nl := nl) (w := w)).slot
      (msgPoint ctx (fun _ => withResponse (nl := nl) (w := w) msgs response) ()
        (querySlot nl w))
  rw [slot_msgPoint ctx _ () hquery]
  simp only [challengeSlot, querySlot]
  omega

end Prefix

end Lfzk.LigeroTranscriptInputs
