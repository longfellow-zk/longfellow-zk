import LfzkV1.NizkDeployedHashTwoField

/-!
# Addresses of the legacy v7 terminal pair

The batching address is the hash prefix with the final message defaulted.
The opening address is the same prefix with the serialized response in
that slot. Thus an observed opening identifies its own batching point,
regardless of query order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.TerminalPrefix125

open LfzkV1.NizkDeployedHash LfzkV1.NizkGrinding
open LfzkV1.NizkDeployedHashTwoField

variable {Ctx Msg Reply : Type} [Inhabited Msg]
variable {nl : ℕ} {widths : ℕ → ℕ}

local notation "Point" => MPoint Ctx Msg nl widths
local notation "Role" => Rounds.Role nl widths

abbrev openingIndex {nl : ℕ} {widths : ℕ → ℕ} : Fin (Rounds.Role.length nl widths) :=
  (Rounds.Role.ligeroQuery : Rounds.Role nl widths).index

local notation "last" => openingIndex (nl := nl) (widths := widths)

/-- Well-formed batching addresses have no opening payload. -/
abbrev BatchPrefix (Ctx Msg : Type) [Inhabited Msg] (nl : ℕ) (widths : ℕ → ℕ) :=
  {p : MPoint Ctx Msg nl widths // p.role = .ligeroChallenge ∧
    p.msgs (Rounds.Role.ligeroQuery (nl := nl) (w := widths)).index = default}

abbrev OpeningPoint (Ctx Msg : Type) (nl : ℕ) (widths : ℕ → ℕ) :=
  {p : MPoint Ctx Msg nl widths // p.role = .ligeroQuery}

noncomputable instance [Fintype Ctx] [Fintype Msg] : Fintype (BatchPrefix Ctx Msg nl widths) := by
  classical
  exact Fintype.ofFinite _

noncomputable instance [Fintype Ctx] [Fintype Msg] : Fintype (OpeningPoint Ctx Msg nl widths) := by
  classical
  exact Fintype.ofFinite _

local notation "Batch" => BatchPrefix Ctx Msg nl widths
local notation "Opening" => OpeningPoint Ctx Msg nl widths

/-- The payload index is the final index of the entire schedule. -/
theorem index_le_opening (j : Fin (Rounds.Role.length nl widths)) : j.val ≤ (last).val := by
  have hj := j.isLt
  simp only [Rounds.Role.length] at hj
  change j.val ≤ Rounds.Role.layerBase widths nl + 2
  omega

/-- Apart from the final payload, every index is at or before batching. -/
theorem index_le_batch_of_ne_opening (j : Fin (Rounds.Role.length nl widths)) (hne : j ≠ last) :
    j.val ≤ (Rounds.Role.ligeroChallenge : Role).slot := by
  have hj := index_le_opening j
  have hlt : j.val < (last).val := by
    exact lt_of_le_of_ne hj (fun h => hne (Fin.ext h))
  change j.val ≤ Rounds.Role.layerBase widths nl + 1
  change j.val < Rounds.Role.layerBase widths nl + 2 at hlt
  omega

private theorem roleAt_own_slot (r : Role) : roleAt r.slot = r := by
  unfold roleAt
  rw [dif_pos r.slot_lt]
  exact indexEquiv_symm_index r

/-- Restore the batching address from any opening address. -/
def parent (o : Opening) : Batch :=
  ⟨⟨o.val.ctx, .ligeroChallenge, Function.update o.val.msgs last default⟩,
    rfl, Function.update_self _ _ _⟩

/-- A complete mathematical response fixes the last raw message at each
prefix. The encoder may depend on that prefix. -/
def openAt (encode : Batch → Reply → Msg) (p : Batch) (u : Reply) : Opening :=
  ⟨⟨p.val.ctx, .ligeroQuery, Function.update p.val.msgs last (encode p u)⟩, rfl⟩

private theorem eq_point {p q : Point} (hctx : p.ctx = q.ctx) (hrole : p.role = q.role)
    (hmsgs : p.msgs = q.msgs) : p = q := by
  apply MPoint.equiv.injective
  exact Prod.ext hctx (Prod.ext hrole hmsgs)

@[simp] theorem parent_openAt (encode : Batch → Reply → Msg) (p : Batch) (u : Reply) :
    parent (openAt encode p u) = p := by
  apply Subtype.ext
  refine eq_point (p := (parent (openAt encode p u)).val) (q := p.val) rfl p.property.1.symm ?_
  funext j
  by_cases hj : j = last
  · subst j
    change Function.update (Function.update p.val.msgs last (encode p u)) last default last =
      p.val.msgs last
    rw [Function.update_self, p.property.2]
  · change Function.update (Function.update p.val.msgs last (encode p u)) last default j =
      p.val.msgs j
    rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- The paired address map is injective, with only per-prefix payload
injectivity. No alternative raw encodings multiply the response mass. -/
theorem openAt_injective (encode : Batch → Reply → Msg)
    (hencode : ∀ p, Function.Injective (encode p)) :
    Function.Injective (fun i : Batch × Reply => openAt encode i.1 i.2) := by
  intro ⟨p, u⟩ ⟨p', u'⟩ h
  have hp : p = p' := by simpa only [parent_openAt] using congrArg parent h
  subst p'
  have hlast := congrArg (fun o : Opening => o.val.msgs last) h
  have hh : encode p u = encode p u' := by
    simpa only [openAt, Function.update_self] using hlast
  exact Prod.ext rfl (hencode p hh)

/-- A decoded alphabet with a left inverse supplies the needed
per-prefix injectivity. -/
theorem openAt_injective_of_decoder (encode : Batch → Reply → Msg)
    (decode : Batch → Msg → Option Reply)
    (hdecode : ∀ p u, decode p (encode p u) = some u) :
    Function.Injective (fun i : Batch × Reply => openAt encode i.1 i.2) := by
  apply openAt_injective encode
  intro p u v h
  exact Option.some.inj ((hdecode p u).symm.trans ((congrArg (decode p) h).trans (hdecode p v)))

/-- Reconstruct an arbitrary valid opening, using its decoded response.
The wire assumption is required only for valid raw messages at that prefix. -/
theorem openAt_eq_of_valid (encode : Batch → Reply → Msg)
    (decode : Batch → Msg → Option Reply) (valid : Batch → Msg → Prop)
    (hvalid : ∀ p m u, valid p m → decode p m = some u → encode p u = m)
    (o : Opening) (u : Reply)
    (hm : valid (parent o) (o.val.msgs last))
    (hread : decode (parent o) (o.val.msgs last) = some u) :
    openAt encode (parent o) u = o := by
  apply Subtype.ext
  refine eq_point (p := (openAt encode (parent o) u).val) (q := o.val) rfl o.property.symm ?_
  funext j
  have hw := hvalid (parent o) (o.val.msgs last) u hm hread
  change Function.update (Function.update o.val.msgs last default) last (encode (parent o) u) j = _
  rw [hw]
  by_cases hj : j = last
  · subst j
    rw [Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

/-- Resetting the last message gives exactly the batching ancestor, even
for an opening address chosen by the adversary. -/
theorem parent_eq_ancestor (o : Opening) :
    (parent o).val = mpoints.anc o.val (Rounds.Role.ligeroChallenge : Role).slot := by
  apply eq_point
  · rfl
  · exact (roleAt_own_slot _).symm
  · funext j
    change Function.update o.val.msgs last default j =
      padMsgs o.val.msgFn (Rounds.Role.ligeroChallenge : Role).slot j
    by_cases hj : j = last
    · subst j
      have hlt := Rounds.Role.ligeroChallenge_lt_ligeroQuery (nl := nl) (w := widths)
      simp only [Function.update_self, padMsgs, Rounds.Role.index, if_neg (Nat.not_le_of_lt hlt)]
    · rw [Function.update_of_ne hj]
      have hlt := index_le_batch_of_ne_opening j hj
      simp only [padMsgs, if_pos hlt, MPoint.msgFn, dif_pos j.isLt]

/-- The verifier's submitted opening is a legal member of the address family. -/
noncomputable def openingOfMessages (ctx : Ctx) (msgs : ℕ → Msg) : Opening :=
  ⟨msgPoint ctx (fun f k => f k) msgs (Rounds.Role.ligeroQuery : Role).slot,
    roleAt_own_slot _⟩

/-- The address family uses the actual batching prefix of the submitted proof. -/
theorem parent_of_submitted_opening (ctx : Ctx) (msgs : ℕ → Msg) :
    (parent (openingOfMessages (nl := nl) (widths := widths) ctx msgs)).val =
      msgPoint ctx (fun f k => f k) msgs (Rounds.Role.ligeroChallenge : Role).slot := by
  rw [parent_eq_ancestor]
  exact anc_msgPoint ctx (fun f k => f k) msgs Rounds.Role.ligeroChallenge_lt_ligeroQuery
    (Rounds.Role.ligeroQuery : Role).slot_lt

section TwoField

open LfzkV1.NizkAdaptiveTwoField (SideCtx)

variable {D K Early SigMsg : Type} {nlS : ℕ} {widthsS : ℕ → ℕ}
local notation "HashCtx" => SideCtx D K Early
local notation "Prefix" => BatchPrefix HashCtx Msg nl widths
local notation "Pt2'" => Pt2 D K Early Msg SigMsg nl nlS widths widthsS

/-- The batching address in the joint two-field transcript. -/
def batchAddress (p : Prefix) : Pt2' := Sum.inr (Sum.inl p.val)

/-- The terminal address in the joint two-field transcript. -/
def openAddress (encode : Prefix → Reply → Msg) (p : Prefix) (u : Reply) : Pt2' :=
  Sum.inr (Sum.inl (openAt encode p u).val)

theorem batchAddress_injective :
    Function.Injective (batchAddress (D := D) (K := K) (Early := Early) (Msg := Msg)
      (nl := nl) (widths := widths) (SigMsg := SigMsg) (nlS := nlS) (widthsS := widthsS)) := by
  intro p p' h
  exact Subtype.ext (Sum.inl.inj (Sum.inr.inj h))

theorem openAddress_injective (encode : Prefix → Reply → Msg)
    (decode : Prefix → Msg → Option Reply)
    (hdecode : ∀ p u, decode p (encode p u) = some u) :
    Function.Injective (fun i : Prefix × Reply =>
      (openAddress encode i.1 i.2 : Pt2')) := by
  intro i j h
  exact openAt_injective_of_decoder encode decode hdecode (Subtype.ext (Sum.inl.inj (Sum.inr.inj h)))

theorem batch_open_ne (encode : Prefix → Reply → Msg) (p p' : Prefix) (u : Reply) :
    (batchAddress p : Pt2') ≠ openAddress encode p' u := by
  intro h
  have h' := congrArg MPoint.role (Sum.inl.inj (Sum.inr.inj h))
  rw [p.property.1, (openAt encode p' u).property] at h'
  cases h'

/-- Both replies are measured against the same Merkle cut. -/
theorem batch_open_same_key (encode : Prefix → Reply → Msg) (p : Prefix) (u : Reply) :
    key2 (batchAddress p : Pt2') = key2 (openAddress encode p u : Pt2') := rfl

end TwoField

end LfzkV1.TerminalPrefix125
