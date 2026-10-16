import Lfzk.RbrZkPotentialPath
import Lfzk.NizkZkTwoField

/-!
# Uniform graded budgets for a compiled Longfellow side

The field-round budget remains specific to the role.  Only the two terminal
budgets are supplied by the agreement curve.  They are uniform in the
commitment context, which is required by adaptive Fiat--Shamir counting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrZkSplit Lfzk.RbrLayerStepS Lfzk.NizkZk
  Lfzk.NizkZkTwoField Lfzk.RbrZkLongfellow Lfzk.CertifiedV1
open scoped Classical

variable {R : Lfzk.CertifiedV1.Row} {logv : ℕ}
variable {Sig C F X Q Msg Witness Ctx : Type}
  [Fintype C] [DecidableEq C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Inhabited Msg]
variable {M ninp logw logc : ℕ}
variable (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)

/-- Changing the final query budget has no effect on a pre-terminal role. -/
theorem mixedBudget_field_query_irrelevant
    {nl : ℕ} {w : ℕ → ℕ} (cand bpair bround bin bquery : ℕ)
    (rl : Rounds.Role nl w)
    (hf : rl.slot < Rounds.Role.layerBase w nl + 1) :
    mixedBudget cand bpair bround bin 0 bquery rl =
      mixedBudget cand bpair bround bin 0 0 rl := by
  cases rl with
  | layerPair _ => rfl
  | sumcheck _ _ => rfl
  | inputBind => rfl
  | ligeroChallenge =>
      simp only [Rounds.Role.slot] at hf
      omega
  | ligeroQuery =>
      simp only [Rounds.Role.slot] at hf
      omega

/-- A side's context-independent role budget.  The three field classes
retain their distinct exact integer counts. -/
noncomputable def sideUniformPotentialBudget
    (βchallenge βquery : ℚ)
    (p : Lfzk.NizkDeployedHash.MPoint Ctx Msg R.params.nl R.params.rounds) : ℚ :=
  if p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1 then
    (mixedBudget R.cardCand
      (zkPairBudget (Fintype.card C) R.params.row.fieldSize logv)
      (pairBudget (Fintype.card C) R.params.row.fieldSize)
      (inBudget (Fintype.card C) R.params.row.fieldSize)
      0 0 p.role : ℚ)
  else if p.role.slot = Rounds.Role.layerBase R.params.rounds R.params.nl + 1 then
    βchallenge else βquery

/-- The role-only form of the side budget; contexts and message prefixes do
not affect the count. -/
noncomputable def sideUniformRoleBudget (βchallenge βquery : ℚ)
    (rl : Rounds.Role R.params.nl R.params.rounds) : ℚ :=
  if rl.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1 then
    (mixedBudget R.cardCand
      (zkPairBudget (Fintype.card C) R.params.row.fieldSize logv)
      (pairBudget (Fintype.card C) R.params.row.fieldSize)
      (inBudget (Fintype.card C) R.params.row.fieldSize)
      0 0 rl : ℚ)
  else if rl.slot = Rounds.Role.layerBase R.params.rounds R.params.nl + 1 then
    βchallenge else βquery

omit [DecidableEq C] [Inhabited Msg] in
theorem sideUniformPotentialBudget_eq_role (βchallenge βquery : ℚ)
    (p : Lfzk.NizkDeployedHash.MPoint Ctx Msg R.params.nl R.params.rounds) :
    sideUniformPotentialBudget (R := R) (logv := logv) (C := C)
      βchallenge βquery p =
      sideUniformRoleBudget (R := R) (logv := logv) (C := C)
        βchallenge βquery p.role := rfl

/-- Exact integer field-slot counts, viewed as a rational total. -/
def sideFieldSlotBudget (R : Lfzk.CertifiedV1.Row)
    (logv cardC : ℕ) : ℚ :=
  (R.params.nl : ℚ) *
      (R.cardCand * zkPairBudget cardC R.params.row.fieldSize logv : ℕ) +
    (∑ ly : Fin R.params.nl, (R.params.rounds ly.val : ℚ)) *
      (R.cardCand * pairBudget cardC R.params.row.fieldSize : ℕ) +
    (R.cardCand * inBudget cardC R.params.row.fieldSize : ℕ)

/-- The exact field-slot count is bounded by the row's field density for
every challenge alphabet size.  This lets the graded numerical certificates
apply without assuming that the combined FS answer has field cardinality. -/
theorem sideFieldSlotBudget_le_density (R : Lfzk.CertifiedV1.Row)
    (logv cardC : ℕ) (hF : 0 < R.params.row.fieldSize) :
    sideFieldSlotBudget R logv cardC ≤
      (cardC : ℚ) * (R.cardCand : ℚ) * zkFieldDensity R logv := by
  let c : ℚ := cardC
  let f : ℚ := R.params.row.fieldSize
  have hbz : (zkPairBudget cardC R.params.row.fieldSize logv : ℚ) ≤
      c * (((logv + 2 : ℕ) : ℚ) / f) := by
    unfold zkPairBudget
    refine le_trans Nat.cast_div_le (le_of_eq ?_)
    push_cast
    ring
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤
      c * (2 / f) := by
    unfold pairBudget
    refine le_trans Nat.cast_div_le (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤
      c * (1 / f) := by
    unfold inBudget
    refine le_trans Nat.cast_div_le (le_of_eq ?_)
    ring
  have hs : (∑ ly : Fin R.params.nl, (R.params.rounds ly.val : ℚ)) =
      (R.params.totalRounds : ℚ) := by
    exact_mod_cast (show (∑ ly : Fin R.params.nl, R.params.rounds ly.val) =
      R.params.totalRounds by
        rw [Fin.sum_univ_eq_sum_range]
        rfl)
  have h1 := mul_le_mul_of_nonneg_left hbz
    (Nat.cast_nonneg R.params.nl : (0 : ℚ) ≤ R.params.nl)
  have h2 := mul_le_mul_of_nonneg_left hbp
    (Nat.cast_nonneg R.params.totalRounds : (0 : ℚ) ≤ R.params.totalRounds)
  have hsum :
      (R.params.nl : ℚ) *
          (zkPairBudget cardC R.params.row.fieldSize logv : ℚ) +
        (R.params.totalRounds : ℚ) *
          (pairBudget cardC R.params.row.fieldSize : ℚ) +
        (inBudget cardC R.params.row.fieldSize : ℚ) ≤
      c * zkFieldDensity R logv := by
    have hf : (0 : ℚ) < f := by
      change (0 : ℚ) < (R.params.row.fieldSize : ℚ)
      exact_mod_cast hF
    have hrhs : c * zkFieldDensity R logv =
        (R.params.nl : ℚ) * (c * (((logv + 2 : ℕ) : ℚ) / f)) +
          (R.params.totalRounds : ℚ) * (c * (2 / f)) + c * (1 / f) := by
      unfold zkFieldDensity
      push_cast
      field_simp
      ring
    rw [hrhs]
    linarith
  have hk := mul_le_mul_of_nonneg_left hsum
    (Nat.cast_nonneg R.cardCand : (0 : ℚ) ≤ R.cardCand)
  unfold sideFieldSlotBudget
  rw [hs]
  push_cast
  nlinarith [hk]

/-- Worst field-role count for a side, before the two graded terminal slots. -/
def sideFieldMaxBudget (R : Lfzk.CertifiedV1.Row)
    (logv cardC : ℕ) : ℕ :=
  Lfzk.NizkGrinding.maxBudget
    (R.cardCand * zkPairBudget cardC R.params.row.fieldSize logv)
    (R.cardCand * pairBudget cardC R.params.row.fieldSize)
    (R.cardCand * inBudget cardC R.params.row.fieldSize) 0 0

/-- The field-only worst slot is bounded by the existing per-query density,
uniformly in the size of the combined challenge alphabet. -/
theorem sideFieldMaxBudget_le_density (R : Lfzk.CertifiedV1.Row)
    (logv cardC : ℕ) (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) :
    (sideFieldMaxBudget R logv cardC : ℚ) ≤
      (cardC : ℚ) * zkMaxDensityAt R logv R.cardCand := by
  have hm : sideFieldMaxBudget R logv cardC ≤
      Lfzk.NizkGrinding.maxBudget
        (R.cardCand * zkPairBudget cardC R.params.row.fieldSize logv)
        (R.cardCand * pairBudget cardC R.params.row.fieldSize)
        (R.cardCand * inBudget cardC R.params.row.fieldSize)
        (ligBudget R.params.row cardC)
        (queryBudget R.params.row cardC) := by
    unfold sideFieldMaxBudget Lfzk.NizkGrinding.maxBudget
    omega
  exact (Nat.cast_le.mpr hm).trans
    (Lfzk.NizkZk.maxBudget_le_zkDensity R logv
      (cardC := cardC) (cardCand := R.cardCand) hC hF)

omit [DecidableEq C] [Inhabited Msg] in
/-- A context-independent maximum for every role's rational budget. -/
theorem sideUniformRoleBudget_le_max (βchallenge βquery : ℚ)
    (rl : Rounds.Role R.params.nl R.params.rounds) :
    sideUniformRoleBudget (R := R) (logv := logv) (C := C)
      βchallenge βquery rl ≤
    max (sideFieldMaxBudget R logv (Fintype.card C) : ℚ)
      (max βchallenge βquery) := by
  unfold sideUniformRoleBudget
  by_cases hf : rl.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1
  · rw [if_pos hf]
    have hn : mixedBudget R.cardCand
        (zkPairBudget (Fintype.card C) R.params.row.fieldSize logv)
        (pairBudget (Fintype.card C) R.params.row.fieldSize)
        (inBudget (Fintype.card C) R.params.row.fieldSize)
        0 0 rl ≤ sideFieldMaxBudget R logv (Fintype.card C) := by
      simpa only [mixedBudget, sideFieldMaxBudget] using
        (Lfzk.NizkGrinding.classBudget_le_max (nl := R.params.nl)
          (w := R.params.rounds) (bpair := R.cardCand *
            zkPairBudget (Fintype.card C) R.params.row.fieldSize logv)
          (bround := R.cardCand *
            pairBudget (Fintype.card C) R.params.row.fieldSize)
          (bin := R.cardCand *
            inBudget (Fintype.card C) R.params.row.fieldSize)
          (blig := 0) (bquery := 0) rl)
    exact (Nat.cast_le.mpr hn).trans (le_max_left _ _)
  · rw [if_neg hf]
    by_cases hc : rl.slot = Rounds.Role.layerBase R.params.rounds R.params.nl + 1
    · rw [if_pos hc]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · rw [if_neg hc]
      exact le_trans (le_max_right _ _) (le_max_right _ _)

omit [DecidableEq C] [Inhabited Msg] in
/-- Exact sum of the rational potential budgets across a side's schedule. -/
theorem sideUniformRoleBudget_sum (βchallenge βquery : ℚ) :
    ∑ i : Fin (Rounds.Role.length R.params.nl R.params.rounds),
      sideUniformRoleBudget (R := R) (logv := logv) (C := C)
        βchallenge βquery (Rounds.Role.indexEquiv.symm i) =
    sideFieldSlotBudget R logv (Fintype.card C) +
      βchallenge + βquery := by
  rw [Rounds.Role.sum_slot_eq_sum_role]
  apply Rounds.Role.sum_role_const_rat
  · intro ly
    have hf := Rounds.Role.layer_slot_lt (w := R.params.rounds) ly
      (k := 0) (by omega)
    simp only [sideUniformRoleBudget, Rounds.Role.slot]
    rw [if_pos (by omega)]
    rfl
  · intro ly j
    have hf := Rounds.Role.layer_slot_lt (w := R.params.rounds) ly
      (k := 1 + j.val) (by omega)
    simp only [sideUniformRoleBudget, Rounds.Role.slot]
    rw [if_pos (by omega)]
    rfl
  · simp [sideUniformRoleBudget, Rounds.Role.slot, mixedBudget,
      RbrLayerStep.classBudget]
  · simp [sideUniformRoleBudget, Rounds.Role.slot]
  · simp [sideUniformRoleBudget, Rounds.Role.slot]

omit [DecidableEq C] [Inhabited Msg] in
theorem sideUniformPotentialBudget_nonneg
    (βchallenge βquery : ℚ) (hc : 0 ≤ βchallenge) (hq : 0 ≤ βquery)
    (p : Lfzk.NizkDeployedHash.MPoint Ctx Msg R.params.nl R.params.rounds) :
    0 ≤ sideUniformPotentialBudget (R := R) (logv := logv)
      (C := C) βchallenge βquery p := by
  unfold sideUniformPotentialBudget
  split_ifs <;> positivity

omit [DecidableEq C] in
/-- The existing field budgets and the graded terminal certificate imply
one local bound at every deployed side hash input. -/
theorem sidePointCharge_uniform_local
    (hF : Fintype.card F = R.params.row.fieldSize)
    (P : ∀ σ, TerminalPotential (S.LD σ))
    (βchallenge βquery : ℚ)
    (hc : ∀ σ, (P σ).challengeBudget ≤ βchallenge)
    (hq : ∀ σ, (P σ).queryBudget ≤ βquery)
    (σ : Sig)
    (p : Lfzk.NizkDeployedHash.MPoint Ctx Msg R.params.nl R.params.rounds)
    (pref : Fin p.role.slot → C) :
    (∑ c : C, sidePointCharge (H := S.H σ) (Sat := S.Sat σ)
      (S.LD σ) (P σ) p pref c) ≤
      sideUniformPotentialBudget (R := R) (logv := logv)
        (C := C) βchallenge βquery p := by
  let bpair := zkPairBudget (Fintype.card C) R.params.row.fieldSize logv
  let bround := pairBudget (Fintype.card C) R.params.row.fieldSize
  let bin := inBudget (Fintype.card C) R.params.row.fieldSize
  have hB := S.budgets hF σ
  have hl := sidePointCharge_local (S.FD σ) (S.LD σ) (P σ) hB p pref
  by_cases hf : p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1
  · rw [if_pos hf] at hl
    have hmono := mixedBudget_mono (S.hcand σ) bpair bround bin 0
      ((S.FD σ).kq * Fintype.card Q) p.role
    have hdrop := mixedBudget_field_query_irrelevant R.cardCand bpair bround bin
      ((S.FD σ).kq * Fintype.card Q) p.role hf
    have hqmono :
        ((mixedBudget (Fintype.card (S.Lift σ)) bpair bround bin 0
          ((S.FD σ).kq * Fintype.card Q) p.role : ℕ) : ℚ) ≤
        (mixedBudget R.cardCand bpair bround bin 0 0 p.role : ℚ) := by
      exact_mod_cast hmono.trans_eq hdrop
    simpa [sideUniformPotentialBudget, hf] using hl.trans hqmono
  · rw [if_neg hf] at hl
    by_cases hcrole : p.role.slot = Rounds.Role.layerBase R.params.rounds R.params.nl + 1
    · rw [if_pos hcrole] at hl
      simpa [sideUniformPotentialBudget, hf, hcrole] using hl.trans (hc σ)
    · rw [if_neg hcrole] at hl
      simpa [sideUniformPotentialBudget, hf, hcrole] using hl.trans (hq σ)

omit [DecidableEq C] in
/-- Only field roles contribute when the terminal V1 pair is bounded
separately.  No terminal-potential budget is needed for this local count. -/
theorem sideFieldPointCharge_uniform_local
    (hF : Fintype.card F = R.params.row.fieldSize)
    (P : ∀ σ, TerminalPotential (S.LD σ))
    (σ : Sig)
    (p : Lfzk.NizkDeployedHash.MPoint Ctx Msg R.params.nl R.params.rounds)
    (pref : Fin p.role.slot → C) :
    (∑ c : C, sideFieldPointCharge (H := S.H σ) (Sat := S.Sat σ)
      (S.LD σ) (P σ) p pref c) ≤
      sideUniformPotentialBudget (R := R) (logv := logv)
        (C := C) 0 0 p := by
  by_cases hf : p.role.slot < Rounds.Role.layerBase R.params.rounds R.params.nl + 1
  · simp only [sideFieldPointCharge, if_pos hf]
    let bpair := zkPairBudget (Fintype.card C) R.params.row.fieldSize logv
    let bround := pairBudget (Fintype.card C) R.params.row.fieldSize
    let bin := inBudget (Fintype.card C) R.params.row.fieldSize
    have hB := S.budgets hF σ
    have hl := sidePointCharge_local (S.FD σ) (S.LD σ) (P σ) hB p pref
    rw [if_pos hf] at hl
    have hmono := mixedBudget_mono (S.hcand σ) bpair bround bin 0
      ((S.FD σ).kq * Fintype.card Q) p.role
    have hdrop := mixedBudget_field_query_irrelevant R.cardCand bpair bround bin
      ((S.FD σ).kq * Fintype.card Q) p.role hf
    have hqmono :
        ((mixedBudget (Fintype.card (S.Lift σ)) bpair bround bin 0
          ((S.FD σ).kq * Fintype.card Q) p.role : ℕ) : ℚ) ≤
        (mixedBudget R.cardCand bpair bround bin 0 0 p.role : ℚ) := by
      exact_mod_cast hmono.trans_eq hdrop
    simpa [sideUniformPotentialBudget, hf] using hl.trans hqmono
  · simp [sideFieldPointCharge, hf, sideUniformPotentialBudget]

end Lfzk.RbrZkFlat
