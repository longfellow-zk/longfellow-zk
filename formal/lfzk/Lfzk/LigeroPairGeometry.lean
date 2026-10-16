import Lfzk.LigeroTranscriptInputs
import Bcs.FirstPairCombined

/-! Canonical prefix coordinates for the V1 challenge/response hash pair. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroPairGeometry

open Lfzk.NizkDeployedHash Lfzk.LigeroTranscriptInputs
open scoped Classical

variable {Ctx Other F : Type} {nl block dblock r : ℕ} {w : ℕ → ℕ}
  [Inhabited Other]

private def cslot (nl : ℕ) (w : ℕ → ℕ) : ℕ :=
  Rounds.Role.layerBase w nl + 1

private def qslot (nl : ℕ) (w : ℕ → ℕ) : ℕ :=
  Rounds.Role.layerBase w nl + 2

/-- A context and precisely the messages available at the V1 challenge. -/
abbrev ParentPrefix :=
  Ctx × (Fin (qslot nl w) →
    Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))

private def prefixMsgs
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w))
    (i : ℕ) : Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r) :=
  if h : i < qslot nl w then p.2 ⟨i, h⟩ else default

/-- The canonical prefix extracted from a prover's message schedule. -/
def ofMessages (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) :
    ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w) :=
  (ctx, fun j => msgs j.val)

theorem prefixMsgs_ofMessages (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (j : ℕ) (hj : j < qslot nl w) :
    prefixMsgs (ofMessages (nl := nl) (w := w) ctx msgs) j = msgs j := by
  simp [prefixMsgs, ofMessages, hj]

noncomputable def parent
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w)) :
    MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w :=
  parentPoint p.1 (prefixMsgs p)

noncomputable def child
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w :=
  childPoint p.1 (prefixMsgs p) response

/-- Every parent challenge point has the V1 challenge round role. -/
theorem parent_slot
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w)) :
    (parent p).role.slot = cslot nl w := by
  have hc : cslot nl w < Rounds.Role.length nl w := by
    simp [cslot, Rounds.Role.length]
  exact slot_msgPoint p.1 (fun _ => prefixMsgs p) () hc

/-- Every child query point has the V1 query round role. -/
theorem child_slot
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    (child p response).role.slot = qslot nl w := by
  have hq : qslot nl w < Rounds.Role.length nl w := by
    simp [qslot, Rounds.Role.length]
  exact slot_msgPoint p.1
    (fun _ => withResponse (nl := nl) (w := w) (prefixMsgs p) response) () hq

/-- All oracle answers outside the two Ligero terminal roles.  In
particular this includes prior field-challenge answers even when the prover
queries them after a Ligero point. -/
abbrev OutsideTerminal :=
  {z : MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w //
    z.role.slot ≠ cslot nl w ∧ z.role.slot ≠ qslot nl w}

def outsideTerminal {Coin : Type}
    (H : MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w → Coin) :
    OutsideTerminal (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w) → Coin :=
  fun z => H z.1

/-- The outside-terminal state is unchanged when the parent and child
answers are resampled, in either order. -/
theorem outsideTerminal_off {Coin : Type}
    (p : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r)
    (H H' : MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w → Coin)
    (h : ∀ z, z ≠ parent p → z ≠ child p response → H z = H' z) :
    outsideTerminal H = outsideTerminal H' := by
  funext z
  apply h z.1
  · intro hz
    exact z.property.1 (hz ▸ parent_slot p)
  · intro hz
    exact z.property.2 (hz ▸ child_slot p response)

/-- The canonical challenge point is the deployed point of the prover's
message schedule. -/
theorem parent_ofMessages (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) :
    parent (ofMessages (nl := nl) (w := w) ctx msgs) =
      parentPoint (nl := nl) (w := w) ctx msgs := by
  unfold parent parentPoint msgPoint
  congr 1
  funext j
  simp only [padMsgs]
  split_ifs with hj
  · have hslot : j.val ≤ Rounds.Role.layerBase w nl + 1 := hj
    rw [prefixMsgs_ofMessages ctx msgs j.val (by
      dsimp [qslot]
      omega)]
  · rfl

/-- The canonical query point is the deployed point after the complete
four-slice response has been absorbed. -/
theorem child_ofMessages (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r) :
    child (ofMessages (nl := nl) (w := w) ctx msgs) response =
      childPoint (nl := nl) (w := w) ctx msgs response := by
  unfold child childPoint msgPoint
  congr 1
  funext j
  simp only [padMsgs]
  split_ifs with hj
  · by_cases hq : j.val = qslot nl w
    · change j.val = Rounds.Role.layerBase w nl + 2 at hq
      simp [withResponse, hq]
    · have hslot : j.val ≤ Rounds.Role.layerBase w nl + 2 := hj
      have hlt : j.val < qslot nl w := by
        dsimp [qslot] at hq ⊢
        omega
      simp [withResponse, prefixMsgs_ofMessages ctx msgs j.val hlt]
  · rfl

/-- At a well-formed response slot, the canonical child is exactly the
ordinary verifier's query-round hash point. -/
theorem child_ofMessages_eq_msgPoint (ctx : Ctx)
    (msgs : ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (response : ResponsePayload F block dblock r)
    (hresponse : msgs (Rounds.Role.layerBase w nl + 2) = Sum.inr response) :
    child (ofMessages (nl := nl) (w := w) ctx msgs) response =
      msgPoint (nl := nl) (w := w) ctx (fun _ => msgs) ()
        (Rounds.Role.layerBase w nl + 2) := by
  rw [child_ofMessages]
  exact childPoint_eq_msgPoint ctx msgs response hresponse

/-- Read the challenge prefix and transmitted response from a completed
proof.  The response is selected only after the prover has finished. -/
def selectedFromOutput {Out : Type} (ctxOf : Out → Ctx)
    (msgOf : Out → ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (responseOf : Out → ResponsePayload F block dblock r) (out : Out) :
    ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w) ×
      ResponsePayload F block dblock r :=
  (ofMessages (nl := nl) (w := w) (ctxOf out) (msgOf out), responseOf out)

theorem parent_selectedFromOutput {Out : Type} (ctxOf : Out → Ctx)
    (msgOf : Out → ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (responseOf : Out → ResponsePayload F block dblock r) (out : Out) :
    parent (selectedFromOutput (nl := nl) (w := w) ctxOf msgOf responseOf out).1 =
      msgPoint (nl := nl) (w := w) (ctxOf out) msgOf out
        (Rounds.Role.layerBase w nl + 1) := by
  exact parent_ofMessages (ctxOf out) (msgOf out)

theorem child_selectedFromOutput {Out : Type} (ctxOf : Out → Ctx)
    (msgOf : Out → ℕ → Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (responseOf : Out → ResponsePayload F block dblock r) (out : Out)
    (hresponse : msgOf out (Rounds.Role.layerBase w nl + 2) =
      Sum.inr (responseOf out)) :
    child (selectedFromOutput (nl := nl) (w := w)
        ctxOf msgOf responseOf out).1
      (selectedFromOutput (nl := nl) (w := w)
        ctxOf msgOf responseOf out).2 =
      msgPoint (nl := nl) (w := w) (ctxOf out) msgOf out
        (Rounds.Role.layerBase w nl + 2) := by
  exact child_ofMessages_eq_msgPoint (ctxOf out) (msgOf out)
    (responseOf out) hresponse

theorem parent_injective :
    Function.Injective
      (parent (Ctx := Ctx) (Other := Other) (F := F)
        (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w)) := by
  intro p p' h
  have hctx : p.1 = p'.1 := congrArg MPoint.ctx h
  have hmsgs : p.2 = p'.2 := by
    funext i
    have hc : cslot nl w < Rounds.Role.length nl w := by
      simp [cslot, Rounds.Role.length]
    have hi : i.val ≤ cslot nl w := by
      have hlt := i.isLt
      dsimp [qslot, cslot] at hlt ⊢
      omega
    have hmsg := congrArg
      (fun z : MPoint Ctx (Message (Other := Other) (F := F)
        (block := block) (dblock := dblock) (r := r)) nl w =>
        z.msgFn i.val) h
    change (msgPoint p.1 (fun _ => prefixMsgs p) ()
      (cslot nl w)).msgFn i.val =
      (msgPoint p'.1 (fun _ => prefixMsgs p') ()
        (cslot nl w)).msgFn i.val at hmsg
    rw [
      msgFn_msgPoint p.1 (fun _ => prefixMsgs p) () hc hi,
      msgFn_msgPoint p'.1 (fun _ => prefixMsgs p') () hc hi] at hmsg
    simpa [prefixMsgs, qslot] using hmsg
  exact Prod.ext hctx hmsgs

theorem child_injective :
    Function.Injective
      (fun pr : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
          (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w) ×
          ResponsePayload F block dblock r => child pr.1 pr.2) := by
  intro ⟨p, response⟩ ⟨p', response'⟩ h
  have hparent : parent p = parent p' := by
    change parentPoint p.1 (prefixMsgs p) =
      parentPoint p'.1 (prefixMsgs p')
    rw [← parent_eq_child_ancestor p.1 (prefixMsgs p) response,
      ← parent_eq_child_ancestor p'.1 (prefixMsgs p') response']
    exact congrArg
      (fun z => (mpoints (Ctx := Ctx)
        (Msg := Message (Other := Other) (F := F)
          (block := block) (dblock := dblock) (r := r))
        (nl := nl) (w := w)).anc z (cslot nl w)) h
  have hp : p = p' := parent_injective hparent
  subst p'
  have hr : response = response' :=
    childPoint_injective p.1 (prefixMsgs p) h
  simp [hr]

theorem parent_ne_child
    (p p' : ParentPrefix (Ctx := Ctx) (Other := Other) (F := F)
      (nl := nl) (block := block) (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    parent p ≠ child p' response := by
  intro h
  have hc : cslot nl w < Rounds.Role.length nl w := by
    simp [cslot, Rounds.Role.length]
  have hq : qslot nl w < Rounds.Role.length nl w := by
    simp [qslot, Rounds.Role.length]
  have hslots := congrArg
    (fun z : MPoint Ctx (Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r)) nl w => z.role.slot) h
  change (mpoints (Ctx := Ctx)
    (Msg := Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (nl := nl) (w := w)).slot (parent p) =
    (mpoints (Ctx := Ctx)
      (Msg := Message (Other := Other) (F := F)
        (block := block) (dblock := dblock) (r := r))
      (nl := nl) (w := w)).slot (child p' response) at hslots
  change (mpoints (Ctx := Ctx)
    (Msg := Message (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (nl := nl) (w := w)).slot
      (msgPoint p.1 (fun _ => prefixMsgs p) () (cslot nl w)) =
    (mpoints (Ctx := Ctx)
      (Msg := Message (Other := Other) (F := F)
        (block := block) (dblock := dblock) (r := r))
      (nl := nl) (w := w)).slot
        (msgPoint p'.1
          (fun _ => withResponse (nl := nl) (w := w)
            (prefixMsgs p') response) () (qslot nl w)) at hslots
  rw [slot_msgPoint p.1 (fun _ => prefixMsgs p) () hc,
    slot_msgPoint p'.1
      (fun _ => withResponse (nl := nl) (w := w) (prefixMsgs p') response)
      () hq] at hslots
  dsimp [cslot, qslot] at hslots
  omega

end Lfzk.LigeroPairGeometry
