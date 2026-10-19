import Bcs.AffinePotential
import Lfzk.RbrZkPotentialSide

/-! A compiled LFZK side has a genuine local-domain certificate on any
injective embedding of its message-prefix inputs in a shared oracle.
The context may depend on complementary answers, as in cut extraction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.AffineSide
open Finset Bcs.AffineBlock Bcs.TotalOracle
open Lfzk.NizkDeployedHash Lfzk.NizkZkTwoField Lfzk.RbrZkFlat Lfzk.RbrZkSplit
open scoped Classical

noncomputable def sideRate (R : Lfzk.CertifiedV1.Row) (logv cardC : ℕ)
    (bc bq : ℚ) (hc : 0 ≤ bc) (hq : 0 ≤ bq) : Rate := {
  intercept := (sideFieldSlotBudget R logv cardC + bc + bq) / cardC
  slope := max (sideFieldMaxBudget R logv cardC : ℚ) (max bc bq) / cardC
  intercept_nonneg := by unfold sideFieldSlotBudget; positivity
  slope_nonneg := div_nonneg ((Nat.cast_nonneg _).trans (le_max_left _ _)) (Nat.cast_nonneg _) }

/-- Normalize exact alphabet counts without assuming divisibility. -/
theorem sideRate_le_density (R : Lfzk.CertifiedV1.Row) (logv cardC : ℕ)
    (hC : 0 < cardC) (hF : 0 < R.params.row.fieldSize)
    (ec eq : ℚ) (hc : 0 ≤ ec) (hq : 0 ≤ eq)
    (hpc : ec ≤ R.zkCoefficient logv) (hpq : eq ≤ R.zkCoefficient logv) :
    let r := sideRate R logv cardC (cardC * ec) (cardC * eq)
      (mul_nonneg (Nat.cast_nonneg _) hc) (mul_nonneg (Nat.cast_nonneg _) hq)
    r.intercept ≤ R.cardCand * Lfzk.NizkZk.zkFieldDensity R logv + ec + eq ∧
      r.slope ≤ R.zkCoefficient logv := by
  have hcq : (0 : ℚ) < cardC := by exact_mod_cast hC
  have hi := sideFieldSlotBudget_le_density R logv cardC hF
  have hs := sideFieldMaxBudget_le_density R logv cardC hC hF
  dsimp only [sideRate]
  constructor
  · apply (div_le_iff₀ hcq).mpr
    nlinarith
  · apply (div_le_iff₀ hcq).mpr
    apply max_le
    · simpa only [Lfzk.CertifiedV1.Row.zkCoefficient, mul_comm] using hs
    · exact max_le (by nlinarith) (by nlinarith)

variable {R : Lfzk.CertifiedV1.Row} {logv : ℕ}
variable {Sig C F X Q Msg Witness Ctx Hash Out : Type}
  [Fintype C] [Nonempty C] [DecidableEq C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
  [Fintype Ctx] [Fintype Msg] [Fintype Hash] [DecidableEq Hash]
variable {M ninp logw logc : ℕ}
variable (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)

omit [DecidableEq C] in
/-- The actual side LayerStep acceptance with no satisfying extracted
candidate; the preceding sumcheck and terminal Ligero data come from S. -/
theorem side_oracle_sound
    (hF : Fintype.card F = R.params.row.fieldSize)
    (embed : MPoint Ctx Msg R.params.nl R.params.rounds ↪ Hash)
    (domain : Finset Hash) (hmem : ∀ p, embed p ∈ domain)
    (ctx : Out → Ctx) (messages : Out → ℕ → Msg)
    (sigAt : (Hash → C) → Ctx → Sig)
    (hsig : ∀ p H H', AgreeOff (embed p) H H' → sigAt H p.ctx = sigAt H' p.ctx)
    (P : ∀ σ, TerminalPotential (S.LD σ))
    (bc bq : ℚ) (hc : 0 ≤ bc) (hq : 0 ≤ bq)
    (hpc : ∀ σ, (P σ).challengeBudget ≤ bc)
    (hpq : ∀ σ, (P σ).queryBudget ≤ bq) :
    OracleSound domain (fun out H =>
      let σ := sigAt H (ctx out)
      (∀ ℓ, ¬ S.Sat σ ℓ) ∧
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R.params.nl) (w := R.params.rounds) (S.V σ) (S.LD σ) (messages out))
        (fun i => H (embed (msgPoint (ctx out) messages out i.val))))
      (sideRate R logv (Fintype.card C) bc bq hc hq) := by
  let wt := fun (p : MPoint Ctx Msg R.params.nl R.params.rounds) (H : Hash → C) c =>
    let σ := sigAt H p.ctx
    sidePointCharge (H := S.H σ) (Sat := S.Sat σ) (S.LD σ) (P σ) p
      (mpoints.chal (fun p => H (embed p)) p) c
  let budget := sideUniformPotentialBudget (R := R) (logv := logv) (C := C) (Ctx := Ctx) (Msg := Msg) bc bq
  let slots := fun i : Fin (Rounds.Role.length R.params.nl R.params.rounds) =>
    sideUniformRoleBudget (R := R) (logv := logv) (C := C) bc bq (Rounds.Role.indexEquiv.symm i)
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  refine oracle_sound_of_embedded_charges embed domain (fun out k => msgPoint (ctx out) messages out k)
    ?_ wt ?_ ?_ budget ?_ ?_ (sideRate R logv (Fintype.card C) bc bq hc hq) slots ?_ ?_ ?_ _ ?_
  · intro out i j he
    have hs := congrArg (fun p => p.role.slot) he
    change mpoints.slot (msgPoint (ctx out) messages out i.val) =
      mpoints.slot (msgPoint (ctx out) messages out j.val) at hs
    rw [slot_msgPoint _ _ _ i.isLt, slot_msgPoint _ _ _ j.isLt] at hs
    exact Fin.ext hs
  · intro p H H' ho c
    have hr : AgreeOff p (fun p => H (embed p)) (fun p => H' (embed p)) :=
      fun z hz => ho (embed z) (fun he => hz (embed.injective he))
    dsimp only [wt]
    rw [hsig p H H' ho, mpoints.chal_congr hr]
  · intro p H c; exact sidePointCharge_nonneg _ _ _ _ _
  · exact sideUniformPotentialBudget_nonneg bc bq hc hq
  · intro p H; exact sidePointCharge_uniform_local S hF P bc bq hpc hpq _ p _
  · intro p
    simp only [hmem p, if_true, sideRate]
    have h := sideUniformRoleBudget_le_max (R := R) (logv := logv) (C := C) bc bq p.role
    change budget p ≤ _
    dsimp only [budget, sideUniformPotentialBudget_eq_role]
    convert h using 1
    field_simp
  · intro out i
    change sideUniformRoleBudget (R := R) (logv := logv) (C := C) bc bq
      (msgPoint (ctx out) messages out i.val).role ≤ _
    simp [msgPoint, Lfzk.NizkGrinding.roleAt, i.isLt, slots]
  · dsimp only [slots, sideRate]
    rw [sideUniformRoleBudget_sum]
    apply le_of_eq
    field_simp
  · intro out H hf
    have h := accepted_noSat_sideTrace_pays (H := S.H (sigAt H (ctx out)))
      (Sat := S.Sat (sigAt H (ctx out))) (S.LD _) (P _) (ctx out) messages out
      (fun p => H (embed p)) hf.1 hf.2
    exact h

omit [DecidableEq C] in
/-- Field-prefix escape on its own hash domain. Terminal roles have zero
charge and need not belong to the domain. -/
theorem field_oracle_sound
    (hF : Fintype.card F = R.params.row.fieldSize)
    (embed : MPoint Ctx Msg R.params.nl R.params.rounds ↪ Hash)
    (domain : Finset Hash) (hmem : ∀ p, p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1 → embed p ∈ domain)
    (ctx : Out → Ctx) (messages : Out → ℕ → Msg)
    (sigAt : (Hash → C) → Ctx → Sig)
    (hsig : ∀ p H H', AgreeOff (embed p) H H' → sigAt H p.ctx = sigAt H' p.ctx)
    (P : ∀ σ, TerminalPotential (S.LD σ)) :
    OracleSound domain (fun out H =>
      let σ := sigAt H (ctx out)
      fieldPrefixEscape (H := S.H σ) (Sat := S.Sat σ) (S.LD σ) (messages out)
        (Bcs.trunc (fun i : Fin (Rounds.Role.length R.params.nl R.params.rounds) =>
          H (embed (msgPoint (ctx out) messages out i.val)))
          (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) Lfzk.CompiledLongfellow.fieldLen_le))
      (sideRate R logv (Fintype.card C) 0 0 (by norm_num) (by norm_num)) := by
  let wt := fun (p : MPoint Ctx Msg R.params.nl R.params.rounds) (H : Hash → C) c =>
    let σ := sigAt H p.ctx
    sideFieldPointCharge (H := S.H σ) (Sat := S.Sat σ) (S.LD σ) (P σ) p
      (mpoints.chal (fun p => H (embed p)) p) c
  let budget := sideUniformPotentialBudget (R := R) (logv := logv) (C := C) (Ctx := Ctx) (Msg := Msg) 0 0
  let slots := fun i : Fin (Rounds.Role.length R.params.nl R.params.rounds) =>
    sideUniformRoleBudget (R := R) (logv := logv) (C := C) 0 0 (Rounds.Role.indexEquiv.symm i)
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  refine oracle_sound_of_embedded_charges embed domain (fun out k => msgPoint (ctx out) messages out k)
    ?_ wt ?_ ?_ budget ?_ ?_ (sideRate R logv (Fintype.card C) 0 0 (by norm_num) (by norm_num)) slots ?_ ?_ ?_ _ ?_
  · intro out i j he
    have hs := congrArg (fun p => p.role.slot) he
    change mpoints.slot (msgPoint (ctx out) messages out i.val) =
      mpoints.slot (msgPoint (ctx out) messages out j.val) at hs
    rw [slot_msgPoint _ _ _ i.isLt, slot_msgPoint _ _ _ j.isLt] at hs
    exact Fin.ext hs
  · intro p H H' ho c
    have hr : AgreeOff p (fun p => H (embed p)) (fun p => H' (embed p)) :=
      fun z hz => ho (embed z) (fun he => hz (embed.injective he))
    dsimp only [wt]
    rw [hsig p H H' ho, mpoints.chal_congr hr]
  · intro p H c; exact sideFieldPointCharge_nonneg _ _ _ _ _
  · exact sideUniformPotentialBudget_nonneg 0 0 (by norm_num) (by norm_num)
  · intro p H; exact sideFieldPointCharge_uniform_local S hF P _ p _
  · intro p
    by_cases hf : p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1
    · simp only [hmem p hf, if_true, sideRate]
      have h := sideUniformRoleBudget_le_max (R := R) (logv := logv) (C := C) 0 0 p.role
      change budget p ≤ _
      dsimp only [budget, sideUniformPotentialBudget_eq_role]
      convert h using 1
      field_simp
    · have hz : budget p = 0 := by simp [budget, sideUniformPotentialBudget, hf]
      rw [hz]
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (sideRate R logv (Fintype.card C) 0 0 (by norm_num) (by norm_num)).slope_nonneg
      · exact le_rfl
  · intro out i
    change sideUniformRoleBudget (R := R) (logv := logv) (C := C) 0 0
      (msgPoint (ctx out) messages out i.val).role ≤ _
    simp [msgPoint, Lfzk.NizkGrinding.roleAt, i.isLt, slots]
  · dsimp only [slots, sideRate]
    rw [sideUniformRoleBudget_sum]
    apply le_of_eq
    field_simp
  · intro out H hf
    have h := fieldPrefixEscape_sideFieldTrace_pays (H := S.H (sigAt H (ctx out)))
      (Sat := S.Sat (sigAt H (ctx out))) (S.LD _) (P _) (ctx out) messages out
      (fun p => H (embed p)) hf
    simpa only [sideFieldTraceCharge_eq_point, wt, msgPoint] using h

end Lfzk.AffineSide
