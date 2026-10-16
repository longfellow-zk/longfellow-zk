import Lfzk.LigeroPairGeometry
import Lfzk.NizkDeployedHashTwoField

/-! Embed the V1 terminal pair in the full two-side deployed oracle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroPairGeometryTwoSide

open Lfzk.LigeroPairGeometry Lfzk.NizkDeployedHashTwoField
open Lfzk.LigeroTranscriptInputs

variable {D C X Other F Msg₂ : Type} {nl nl₂ block dblock r : ℕ}
  {w w₂ : ℕ → ℕ} [Inhabited Other]

abbrev FirstMessage := Message (Other := Other) (F := F)
  (block := block) (dblock := dblock) (r := r)

abbrev Point := Pt2 D C X
  (FirstMessage (Other := Other) (F := F)
    (block := block) (dblock := dblock) (r := r)) Msg₂ nl nl₂ w w₂

abbrev Prefix := ParentPrefix
  (Ctx := Lfzk.NizkAdaptiveTwoField.SideCtx D C X)
  (Other := Other) (F := F) (nl := nl)
  (block := block) (dblock := dblock) (r := r) (w := w)

noncomputable def parent (p : Prefix (D := D) (C := C) (X := X)
    (Other := Other) (F := F) (nl := nl) (block := block)
    (dblock := dblock) (r := r) (w := w)) :
    Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
      (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) :=
  Sum.inr (Sum.inl (LigeroPairGeometry.parent p))

noncomputable def child (p : Prefix (D := D) (C := C) (X := X)
    (Other := Other) (F := F) (nl := nl) (block := block)
    (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
      (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) :=
  Sum.inr (Sum.inl (LigeroPairGeometry.child p response))

theorem parent_injective : Function.Injective
    (parent (D := D) (C := C) (X := X) (Other := Other) (F := F)
      (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂)) := by
  intro p p' h
  exact LigeroPairGeometry.parent_injective (Sum.inl.inj (Sum.inr.inj h))

theorem child_injective : Function.Injective
    (fun pr : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w) ×
      ResponsePayload F block dblock r => (child pr.1 pr.2 :
      Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
        (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂))) := by
  intro pr pr' h
  exact LigeroPairGeometry.child_injective (Sum.inl.inj (Sum.inr.inj h))

theorem parent_ne_child (p p' : Prefix (D := D) (C := C) (X := X)
    (Other := Other) (F := F) (nl := nl) (block := block)
    (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p ≠
      child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p' response := by
  intro h
  exact LigeroPairGeometry.parent_ne_child p p' response
    (Sum.inl.inj (Sum.inr.inj h))

/-- Both terminal points name the same pair of Merkle roots. -/
theorem key_parent_eq_child (p : Prefix (D := D) (C := C) (X := X)
    (Other := Other) (F := F) (nl := nl) (block := block)
    (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    Lfzk.NizkDeployedHashTwoField.key2
      (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p) =
    Lfzk.NizkDeployedHashTwoField.key2
      (child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p response) := by
  rfl

theorem key_parent (p : Prefix (D := D) (C := C) (X := X)
    (Other := Other) (F := F) (nl := nl) (block := block)
    (dblock := dblock) (r := r) (w := w)) :
    Lfzk.NizkDeployedHashTwoField.key2
      (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p) = p.1.1 := by
  rfl

/-- The deployed two-side setup meets the same-key premise of the adaptive
cut-context theorem. -/
theorem setup2_key_parent_eq_child [Nonempty C] [Inhabited Msg₂]
    {Enc Out : Type} {tA N : ℕ}
    (body : Merkle.RandomOracle.TwoOracleTree Enc D
      (Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
        (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
        (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂))
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (msgOf₂ : Out → ℕ → Msg₂)
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r) :
    (Lfzk.NizkDeployedHashTwoField.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).key
        (parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p) =
    (Lfzk.NizkDeployedHashTwoField.setup2 body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂).key
        (child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p response) := by
  exact key_parent_eq_child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂)
    p response

/-- Every key point, second-side point, and first-side field point is in
this state.  Only first-side challenge/query role points are excluded. -/
abbrev OutsideTerminal :=
  {z : Point (D := D) (C := C) (X := X) (Other := Other) (F := F)
      (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) //
    ∀ p, z = Sum.inr (Sum.inl p) →
      p.role.slot ≠ Rounds.Role.layerBase w nl + 1 ∧
      p.role.slot ≠ Rounds.Role.layerBase w nl + 2}

def outsideTerminal {Coin : Type}
    (H : Point (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → Coin) :
    OutsideTerminal (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → Coin :=
  fun z => H z.1

/-- Each earlier first-side verifier answer is outside the two V1 terminal
roles, even when the prover queried it after a terminal point. -/
noncomputable def fieldAncestor
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w))
    (j : Fin (Rounds.Role.layerBase w nl + 1)) :
    OutsideTerminal (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) := by
  let a := (Lfzk.NizkDeployedHash.mpoints
    (Ctx := Lfzk.NizkAdaptiveTwoField.SideCtx D C X)
    (Msg := FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (nl := nl) (w := w)).anc (Lfzk.LigeroPairGeometry.parent p) j.val
  refine ⟨Sum.inr (Sum.inl a), ?_⟩
  intro q hq
  have heq : a = q := Sum.inl.inj (Sum.inr.inj hq)
  have hjlen : j.val < Rounds.Role.length nl w := by
    have hc : Rounds.Role.layerBase w nl + 1 < Rounds.Role.length nl w := by
      simp [Rounds.Role.length]
    exact lt_trans j.isLt hc
  have haslot : a.role.slot = j.val := by
    exact Lfzk.NizkGrinding.slot_roleAt hjlen
  rw [← heq, haslot]
  constructor <;> omega

noncomputable def fieldTape {Coin : Type}
    (outside : OutsideTerminal (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := block)
      (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → Coin)
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w)) :
    Fin (Rounds.Role.layerBase w nl + 1) → Coin :=
  fun j => outside (fieldAncestor (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p j)

theorem fieldTape_outsideTerminal {Coin : Type}
    (H : Point (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → Coin)
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w))
    (j : Fin (Rounds.Role.layerBase w nl + 1)) :
    fieldTape (outsideTerminal H) p j =
      H (Sum.inr (Sum.inl ((Lfzk.NizkDeployedHash.mpoints
        (Ctx := Lfzk.NizkAdaptiveTwoField.SideCtx D C X)
        (Msg := FirstMessage (Other := Other) (F := F)
          (block := block) (dblock := dblock) (r := r))
        (nl := nl) (w := w)).anc (Lfzk.LigeroPairGeometry.parent p) j.val))) := by
  rfl

/-- The local state's field prefix reads exactly the deployed two-side
verifier's earlier hash inputs. -/
theorem fieldTape_ofMessages_eq_hash2 [Inhabited Msg₂]
    {Out : Type}
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → FirstMessage (Other := Other) (F := F)
      (block := block) (dblock := dblock) (r := r))
    (msgOf₂ : Out → ℕ → Msg₂)
    (H : Point (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → C)
    (out : Out) (j : Fin (Rounds.Role.layerBase w nl + 1)) :
    fieldTape (outsideTerminal H)
      (Lfzk.LigeroPairGeometry.ofMessages (nl := nl) (w := w)
        (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out)
        (msgOf₁ out)) j =
      H (Lfzk.NizkDeployedHashTwoField.hash2
        (nl₁ := nl) (nl₂ := nl₂) (w₁ := w) (w₂ := w₂)
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out (1 + j.val)) := by
  let ctx := Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf out
  have hc : Rounds.Role.layerBase w nl + 1 < Rounds.Role.length nl w := by
    simp [Rounds.Role.length]
  have hparent := Lfzk.LigeroPairGeometry.parent_ofMessages
    (nl := nl) (w := w) ctx (msgOf₁ out)
  have hanc := Lfzk.NizkDeployedHash.anc_msgPoint
    (nl := nl) (w := w) ctx msgOf₁ out j.isLt hc
  have hanc' : (Lfzk.NizkDeployedHash.mpoints
      (Ctx := Lfzk.NizkAdaptiveTwoField.SideCtx D C X)
      (Msg := FirstMessage (Other := Other) (F := F)
        (block := block) (dblock := dblock) (r := r))
      (nl := nl) (w := w)).anc
        (Lfzk.LigeroTranscriptInputs.parentPoint (nl := nl) (w := w)
          ctx (msgOf₁ out)) j.val =
      Lfzk.NizkDeployedHash.msgPoint (nl := nl) (w := w)
        ctx msgOf₁ out j.val := hanc
  have hh := Lfzk.NizkDeployedHashTwoField.hash2_side1
    (nl₁ := nl) (nl₂ := nl₂) (w₁ := w) (w₂ := w₂)
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
    (show j.val < Rounds.Role.length nl w by omega)
  rw [fieldTape_outsideTerminal, hparent]
  rw [hanc', hh]

theorem outsideTerminal_off {Coin : Type}
    (p : Prefix (D := D) (C := C) (X := X)
      (Other := Other) (F := F) (nl := nl) (block := block)
      (dblock := dblock) (r := r) (w := w))
    (response : ResponsePayload F block dblock r)
    (H H' : Point (D := D) (C := C) (X := X) (Other := Other)
      (F := F) (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
      (block := block) (dblock := dblock) (r := r) (w := w) (w₂ := w₂) → Coin)
    (h : ∀ z, z ≠ parent (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p →
      z ≠ child (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := w₂) p response → H z = H' z) :
    outsideTerminal H = outsideTerminal H' := by
  funext z
  apply h z.1
  · intro hz
    exact (z.property (LigeroPairGeometry.parent p) hz).1
      (LigeroPairGeometry.parent_slot p)
  · intro hz
    exact (z.property (LigeroPairGeometry.child p response) hz).2
      (LigeroPairGeometry.child_slot p response)

end Lfzk.LigeroPairGeometryTwoSide
