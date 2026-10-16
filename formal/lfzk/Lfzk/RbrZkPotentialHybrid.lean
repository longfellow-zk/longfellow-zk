import Lfzk.RbrZkPotentialTwoField

/-!
The first (hash) side's terminal V1 event is bounded directly.  This charge
keeps its field escapes and all charges on the signature side and MAC key.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace Lfzk.NizkZkDeployedHash

open Finset Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashTwoField
  Lfzk.RbrZkFlat
  Lfzk.NizkZkTwoField Lfzk.NizkZk
open scoped Classical

variable {R₁ R₂ : Lfzk.CertifiedV1.Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C]
variable {D Enc X : Type} [Fintype X] [DecidableEq X]
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁] [Inhabited Msg₁]
  {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂] [Inhabited Msg₂]
  {M₂ ninp₂ logw₂ logc₂ : ℕ}

private abbrev HKey (D Enc : Type) := (D × D) × List (Enc × D)
private abbrev HSig (D C X Enc : Type) := HKey D Enc × C × X

variable (S₁ : ZkSide R₁ logv₁ (HSig D C X Enc) C F₁ X₁ Q₁ Msg₁ Witness₁
  M₁ ninp₁ logw₁ logc₁)
variable (S₂ : ZkSide R₂ logv₂ (HSig D C X Enc) C F₂ X₂ Q₂ Msg₂ Witness₂
  M₂ ninp₂ logw₂ logc₂)

/-- The merged charge after moving the first side's terminal event to the
direct two-coordinate V1 bound. -/
noncomputable def twoFieldHybridCharge
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (κ : HKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) (c : C) : ℚ :=
  match p with
  | Sum.inl key =>
      twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
        (Sum.inl key) pref c
  | Sum.inr (Sum.inl p₁) =>
      if p₁.role.slot < Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1 then
        twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
          (Sum.inr (Sum.inl p₁)) pref c
      else 0
  | Sum.inr (Sum.inr p₂) =>
      twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt κ
        (Sum.inr (Sum.inr p₂)) pref c

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
theorem twoFieldHybridCharge_nonneg
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (κ : HKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) (c : C) :
    0 ≤ twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt κ p pref c := by
  rcases p with p | p | p
  · exact twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _
  · simp only [twoFieldHybridCharge]
    split_ifs
    · exact twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _
    · exact le_refl _
  · exact twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt κ _ _ _

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Existing side estimates imply the reduced local budget.  Both hash-side
terminal slots are zero, while every other slot retains its old bound. -/
theorem twoFieldHybridCharge_local_of_old
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (keyBudget β₁c β₁q β₂c β₂q : ℚ)
    (hlocal : ∀ (κ : HKey D Enc)
      (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds)
      (pref : Fin (pts2.slot p) → C),
      (∑ c : C, twoFieldPotentialCharge S₁ S₂ P₁ P₂
        keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget
        (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
          (C := C) β₁c β₁q)
        (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
          (C := C) β₂c β₂q) p)
    (κ : HKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldHybridCharge S₁ S₂ P₁ P₂
      keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget
        (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
          (C := C) 0 0)
        (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
          (C := C) β₂c β₂q) p := by
  rcases p with p | p | p
  · simpa only [twoFieldHybridCharge, twoFieldPotentialBudget] using
      hlocal κ (Sum.inl p) pref
  · by_cases hf : p.role.slot <
        Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1
    · have h := hlocal κ (Sum.inr (Sum.inl p)) pref
      simpa [twoFieldHybridCharge, twoFieldPotentialBudget,
        sideUniformPotentialBudget, hf] using h
    · simp [twoFieldHybridCharge, twoFieldPotentialBudget,
        sideUniformPotentialBudget, hf]
  · simpa only [twoFieldHybridCharge, twoFieldPotentialBudget] using
      hlocal κ (Sum.inr (Sum.inr p)) pref

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Concrete side budgets for the hybrid FS charge.  The first side's
challenge and query coefficients disappear from both slot sum and maximum. -/
theorem twoFieldHybridCharge_local_of_sides
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (keyBudget : ℚ)
    (hkey : ∀ κ : HKey D Enc,
      (∑ c : C, if keyBad κ c then (1 : ℚ) else 0) ≤ keyBudget)
    (β₁c β₁q β₂c β₂q : ℚ)
    (hβ₁c : 0 ≤ β₁c) (hβ₁q : 0 ≤ β₁q)
    (hβ₂c : 0 ≤ β₂c) (hβ₂q : 0 ≤ β₂q)
    (hP₁c : ∀ σ, (P₁ σ).challengeBudget ≤ β₁c)
    (hP₁q : ∀ σ, (P₁ σ).queryBudget ≤ β₁q)
    (hP₂c : ∀ σ, (P₂ σ).challengeBudget ≤ β₂c)
    (hP₂q : ∀ σ, (P₂ σ).queryBudget ≤ β₂q)
    (κ : HKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldHybridCharge S₁ S₂ P₁ P₂
      keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget
        (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
          (C := C) 0 0)
        (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
          (C := C) β₂c β₂q) p := by
  exact twoFieldHybridCharge_local_of_old S₁ S₂ P₁ P₂ keyBad dflt
    keyBudget β₁c β₁q β₂c β₂q
    (fun κ p pref =>
      twoFieldPotentialCharge_local_of_sides S₁ S₂ hF₁ hF₂
        P₁ P₂ keyBad dflt keyBudget hkey
        β₁c β₁q β₂c β₂q hβ₁c hβ₁q hβ₂c hβ₂q
        hP₁c hP₁q hP₂c hP₂q κ p pref) κ p pref

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- The first side's terminal event is counted directly, so its potential
can be coarse: only its field-role budgets survive in the hybrid charge. -/
theorem twoFieldHybridCharge_local_coarse_first
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (keyBudget : ℚ)
    (hkey : ∀ κ : HKey D Enc,
      (∑ c : C, if keyBad κ c then (1 : ℚ) else 0) ≤ keyBudget)
    (β₂c β₂q : ℚ)
    (hβ₂c : 0 ≤ β₂c) (hβ₂q : 0 ≤ β₂q)
    (hP₂c : ∀ σ, (P₂ σ).challengeBudget ≤ β₂c)
    (hP₂q : ∀ σ, (P₂ σ).queryBudget ≤ β₂q)
    (κ : HKey D Enc)
    (p : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldHybridCharge S₁ S₂
      (fun σ => TerminalPotential.coarse (S₁.LD σ)) P₂
      keyBad dflt κ p pref c) ≤
      twoFieldPotentialBudget keyBudget
        (sideUniformPotentialBudget (R := R₁) (logv := logv₁)
          (C := C) 0 0)
        (sideUniformPotentialBudget (R := R₂) (logv := logv₂)
          (C := C) β₂c β₂q) p := by
  exact twoFieldHybridCharge_local_of_sides S₁ S₂ hF₁ hF₂
    (fun σ => TerminalPotential.coarse (S₁.LD σ)) P₂ keyBad dflt
    keyBudget hkey 0 (Fintype.card C) β₂c β₂q
    (le_refl _) (by positivity) hβ₂c hβ₂q
    (by intro σ; exact le_refl _)
    (by intro σ; exact le_refl _)
    hP₂c hP₂q κ p pref

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
theorem twoFieldHybridCharge_side1_at
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (κ : HKey D Enc)
    (p : Lfzk.NizkDeployedHash.MPoint
      (Lfzk.NizkAdaptiveTwoField.SideCtx D C X) Msg₁
      R₁.params.nl R₁.params.rounds)
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hfail : ZkFails S₁.Sat
      (κ, p.ctx.2.1, p.ctx.2.2)) :
    twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt κ
      (Sum.inr (Sum.inl p)) (pts2.chal ro (Sum.inr (Sum.inl p)))
      (ro (Sum.inr (Sum.inl p))) =
      sideFieldPointCharge (H := S₁.H (κ, p.ctx.2.1, p.ctx.2.2))
        (Sat := S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2))
        (S₁.LD (κ, p.ctx.2.1, p.ctx.2.2))
        (P₁ (κ, p.ctx.2.1, p.ctx.2.2)) p
        (Lfzk.NizkDeployedHash.mpoints.chal
          (fun q => ro (Sum.inr (Sum.inl q))) p)
        (ro (Sum.inr (Sum.inl p))) := by
  by_cases hf : p.role.slot <
      Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1
  · simpa [twoFieldHybridCharge, sideFieldPointCharge, hf] using
      twoFieldPotentialCharge_side1_at S₁ S₂ P₁ P₂ keyBad dflt κ p ro hfail
  · simp [twoFieldHybridCharge, sideFieldPointCharge, hf]

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
theorem twoFieldHybridCharge_side2_at
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    (κ : HKey D Enc)
    (p : Lfzk.NizkDeployedHash.MPoint
      (Lfzk.NizkAdaptiveTwoField.SideCtx D C X ×
        (Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → Msg₁))
      Msg₂ R₂.params.nl R₂.params.rounds)
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hfail : ZkFails S₂.Sat
      (κ, p.ctx.1.2.1, p.ctx.1.2.2)) :
    twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt κ
      (Sum.inr (Sum.inr p)) (pts2.chal ro (Sum.inr (Sum.inr p)))
      (ro (Sum.inr (Sum.inr p))) =
      sidePointCharge (H := S₂.H (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (Sat := S₂.Sat (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (S₂.LD (κ, p.ctx.1.2.1, p.ctx.1.2.2))
        (P₂ (κ, p.ctx.1.2.1, p.ctx.1.2.2)) p
        (Lfzk.NizkDeployedHash.mpoints.chal
          (fun q => ro (Sum.inr (Sum.inr q))) p)
        (ro (Sum.inr (Sum.inr p))) := by
  simpa only [twoFieldHybridCharge] using
    twoFieldPotentialCharge_side2_at S₁ S₂ P₁ P₂ keyBad dflt κ p ro hfail

omit [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Any nonnegative charge on the merged deployed schedule pays if its key,
first side, or second side component pays. -/
theorem twoField_nonneg_component_path
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out)
    (f : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ)
    (hnonneg : ∀ p, 0 ≤ f p)
    (A B : Prop)
    (hkey : ¬ A → ¬ B → 1 ≤ f (Sum.inl (rootOf₁ out, rootOf₂ out)))
    (hside₁ : A → 1 ≤ ∑ i : Fin
        (Rounds.Role.length R₁.params.nl R₁.params.rounds),
      f (Sum.inr (Sum.inl
        (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf out)
          msgOf₁ out i.val))))
    (hside₂ : B → 1 ≤ ∑ i : Fin
        (Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val)))) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) := by
  rw [sum_hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out f]
  have hk : 0 ≤ f (Sum.inl (rootOf₁ out, rootOf₂ out)) := hnonneg _
  have hs₁ : 0 ≤ ∑ i : Fin
      (Rounds.Role.length R₁.params.nl R₁.params.rounds),
      f (Sum.inr (Sum.inl (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val))) :=
    Finset.sum_nonneg fun i _ => hnonneg _
  have hs₂ : 0 ≤ ∑ i : Fin
      (Rounds.Role.length R₂.params.nl R₂.params.rounds),
      f (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val))) :=
    Finset.sum_nonneg fun i _ => hnonneg _
  by_cases ha : A
  · linarith [hside₁ ha]
  by_cases hb : B
  · linarith [hside₂ hb]
  linarith [hkey ha hb]

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- The reduced merged charge pays on any path with a hash-side field
escape, a failing signature-side extractor, or a MAC key collision. -/
theorem twoFieldHybridCharge_verifier_path
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hside₁ : ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
        sideFieldTraceCharge
          (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
          (fun p => ro (Sum.inr (Sum.inl p))) i)
    (hside₂ : ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      1 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
        sideTraceCharge
          (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out i.val) msgOf₂ out
          (fun p => ro (Sum.inr (Sum.inr p))) i) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  let κ : HKey D Enc := ((rootOf₁ out, rootOf₂ out), cut)
  let σ : HSig D C X Enc := (κ, avOf out, pubOf out)
  let f : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → ℚ :=
    fun p => twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt κ p
      (pts2.chal ro p) (ro p)
  change 1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl
      R₁.params.rounds + Rounds.Role.length R₂.params.nl R₂.params.rounds),
    f (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
  apply twoField_nonneg_component_path rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ out f
    (fun p => twoFieldHybridCharge_nonneg S₁ S₂ P₁ P₂
      keyBad dflt κ p _ _) (ZkFails S₁.Sat σ) (ZkFails S₂.Sat σ)
  · intro hf₁ hf₂
    have hb := hkey hf₁ hf₂
    simp [f, twoFieldHybridCharge, twoFieldPotentialCharge, κ, hb]
  · intro hf₁
    have hp := hside₁ hf₁
    calc
      1 ≤ ∑ i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          sideFieldTraceCharge (H := S₁.H σ) (Sat := S₁.Sat σ)
            (S₁.LD σ) (P₁ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
            (fun p => ro (Sum.inr (Sum.inl p))) i := hp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sideFieldTraceCharge_eq_point]
        exact (twoFieldHybridCharge_side1_at S₁ S₂ P₁ P₂
          keyBad dflt κ _ ro hf₁).symm
  · intro hf₂
    have hp := hside₂ hf₂
    calc
      1 ≤ ∑ i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          sideTraceCharge (H := S₂.H σ) (Sat := S₂.Sat σ)
            (S₂.LD σ) (P₂ σ)
            (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
              fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
                msgOf₁ out j.val) msgOf₂ out
            (fun p => ro (Sum.inr (Sum.inr p))) i := hp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (twoFieldHybridCharge_side2_at S₁ S₂ P₁ P₂
          keyBad dflt κ _ ro hf₂).symm

omit [DecidableEq C] [Fintype X] [DecidableEq X] in
/-- Accepted signature side plus a hash-side field escape imply payment on
the deployed merged path; the hash terminal is outside this charge. -/
theorem twoFieldHybridCharge_accepted_path_of_field
    (P₁ : ∀ σ, TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, TerminalPotential (S₂.LD σ))
    (keyBad : HKey D Enc → C → Prop) (dflt : C)
    {Out : Type} (rootOf₁ rootOf₂ : Out → D)
    (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (out : Out) (cut : List (Enc × D))
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hfield : ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      let tape : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C :=
        fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))
      fieldPrefixEscape
        (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₁ out)
        (Bcs.trunc tape
          (Rounds.Role.layerBase R₁.params.rounds R₁.params.nl + 1)
          (by dsimp [Rounds.Role.length]; omega)))
    (hacc₂ : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl)
        (w := R₂.params.rounds)
        (S₂.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₂ out))
      (fun i => ro (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val))))) :
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
        ((rootOf₁ out, rootOf₂ out), cut)
        (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)
        (pts2.chal ro
          (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val))
        (ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val)) := by
  apply twoFieldHybridCharge_verifier_path S₁ S₂ P₁ P₂ keyBad dflt
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out cut ro hkey
  · intro hf
    exact fieldPrefixEscape_sideFieldTrace_pays
      (H := S₁.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₁.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₁ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out
      (fun p => ro (Sum.inr (Sum.inl p))) (hfield hf)
  · intro hf
    exact accepted_noSat_sideTrace_pays
      (H := S₂.H (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (Sat := S₂.Sat (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (P₂ (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
      (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
        fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          msgOf₁ out j.val) msgOf₂ out
      (fun p => ro (Sum.inr (Sum.inr p))) hf hacc₂

end Lfzk.NizkZkDeployedHash
