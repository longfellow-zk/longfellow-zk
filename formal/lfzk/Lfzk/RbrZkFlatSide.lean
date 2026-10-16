import Lfzk.RbrZkFlatTape
import Lfzk.RbrZkPotentialSide

/-!
# Field-prefix cost of a flat Longfellow side

The field part of the accepted-path split uses the same exact decoder
budgets and candidate-list factor as the existing compiled side.  Its two
terminal Ligero slots are excluded; they are charged jointly by the flat V1
certificate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkFlat

open Finset Lfzk.RbrLayerStepS Lfzk.NizkZk Lfzk.NizkZkTwoField
  Lfzk.RbrZkSplit Lfzk.RbrZkLongfellow Lfzk.CertifiedV1
open scoped Classical

variable {R : Row} {logv : ℕ} {Sig C : Type} [Fintype C] [Nonempty C]
variable {F X Q Msg Witness : Type} [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F] [Fintype X] [DecidableEq X] [Fintype Q] [DecidableEq Q]
variable {M ninp logw logc : ℕ}

/-- The prefix escape of a fixed side and commitment costs at most its
list-scaled field density.  The statement does not include either terminal
Ligero answer. -/
theorem ZkSide.fieldPrefixEscape_ratio_le_density
    (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (σ : Sig) (ms : ℕ → Msg) :
    ((univ.filter fun pref : Fin
      (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) → C =>
        fieldPrefixEscape (H := S.H σ) (Sat := S.Sat σ)
          (S.LD σ) ms pref).card : ℚ) /
      Fintype.card (Fin
        (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) → C) ≤
      (R.cardCand : ℚ) * zkFieldDensity R logv := by
  classical
  let u := Rounds.Role.layerBase R.params.rounds R.params.nl + 1
  let bp := zkPairBudget (Fintype.card C) R.params.row.fieldSize logv
  let br := pairBudget (Fintype.card C) R.params.row.fieldSize
  let bi := inBudget (Fintype.card C) R.params.row.fieldSize
  let bq := (S.FD σ).kq * Fintype.card Q
  have hbud := S.budgets hF σ
  have hp := fieldPrefixEscape_ratio_le (S.FD σ) (S.LD σ) hbud ms
  have hrole (i : Fin u) :
      mixedBudget (Fintype.card (S.Lift σ)) bp br bi 0 bq
        (Rounds.Role.indexEquiv.symm
          (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
            Fin (Rounds.Role.length R.params.nl R.params.rounds))) =
      mixedBudget (Fintype.card (S.Lift σ)) bp br bi 0 0
        (Rounds.Role.indexEquiv.symm
          (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
            Fin (Rounds.Role.length R.params.nl R.params.rounds))) := by
    apply mixedBudget_field_query_irrelevant
    have h := Rounds.Role.indexEquiv.apply_symm_apply
      (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
        Fin (Rounds.Role.length R.params.nl R.params.rounds))
    have hslot :
        (Rounds.Role.indexEquiv.symm
          (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
            Fin (Rounds.Role.length R.params.nl R.params.rounds))).slot = i.val :=
      congrArg Fin.val h
    rw [hslot]
    exact i.isLt
  have hsum :
      (∑ i : Fin u,
        mixedBudget (Fintype.card (S.Lift σ)) bp br bi 0 bq
          (Rounds.Role.indexEquiv.symm
            (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
              Fin (Rounds.Role.length R.params.nl R.params.rounds)))) =
      Fintype.card (S.Lift σ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi) := by
    calc
      _ = ∑ i : Fin u,
          mixedBudget (Fintype.card (S.Lift σ)) bp br bi 0 0
            (Rounds.Role.indexEquiv.symm
              (⟨i.val, by dsimp [Rounds.Role.length, u]; omega⟩ :
                Fin (Rounds.Role.length R.params.nl R.params.rounds))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hrole i
      _ = _ := by
        simpa only [u] using mixed_budget_field_prefix_sum
          (nl := R.params.nl) (w := R.params.rounds)
          (Fintype.card (S.Lift σ)) bp br bi
  have hprefix :
      ((univ.filter fun pref : Fin u → C =>
        fieldPrefixEscape (H := S.H σ) (Sat := S.Sat σ)
          (S.LD σ) ms pref).card : ℚ) /
        Fintype.card (Fin u → C) ≤
      (Fintype.card (S.Lift σ) : ℚ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi) /
          Fintype.card C := by
    simpa only [u, bp, br, bi, bq, hsum, Nat.cast_mul, Nat.cast_add] using hp
  have hcand := S.hcand σ
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hscaled :
      (Fintype.card (S.Lift σ) : ℚ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi) ≤
      (R.cardCand : ℚ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi) := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcand)
    positivity
  have hsum_budget :
      ((R.cardCand : ℚ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi)) =
      sideFieldSlotBudget R logv (Fintype.card C) := by
    have hr : (∑ ly : Fin R.params.nl, (R.params.rounds ly.val : ℚ)) =
        ((∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly : ℕ) : ℚ) := by
      have hn : (∑ ly : Fin R.params.nl, R.params.rounds ly.val) =
          ∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly := by
        rw [Fin.sum_univ_eq_sum_range]
      exact_mod_cast hn
    simp only [sideFieldSlotBudget, bp, br, bi, hr]
    push_cast
    ring
  have hdensity := sideFieldSlotBudget_le_density R logv (Fintype.card C)
    (by rw [← hF]; exact Fintype.card_pos)
  have hfield :
      (Fintype.card (S.Lift σ) : ℚ) *
        (R.params.nl * bp +
          (∑ ly ∈ Finset.range R.params.nl, R.params.rounds ly) * br + bi) /
          Fintype.card C ≤
      (R.cardCand : ℚ) * zkFieldDensity R logv := by
    rw [div_le_iff₀ hC]
    have h := hscaled.trans_eq hsum_budget
    have h' := h.trans hdensity
    nlinarith
  exact hprefix.trans hfield

/-- A conditional bound for the unique built system at a fixed prefix bounds
the terminal event's existential guard. -/
theorem ZkSide.terminalPairAccept_ratio_le_of_built
    (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)
    (σ : Sig) (ms : ℕ → Msg) (terminalBound : ℚ)
    (htermNonneg : 0 ≤ terminalBound)
    (hbuilt : ∀ (pref : Fin
      (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) → C)
      (sys : LigeroSystem ninp M F),
      (chain (nl := R.params.nl) (w := R.params.rounds)
        (S.V σ) (S.H σ) (S.asg σ) (S.Sat σ)
        (flatData (S.LD σ)) ms).state
        (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) pref = .built sys →
      Fits (S.V σ) sys → NoSat (S.asg σ) sys →
      ((univ.filter fun pair : C × C =>
        (S.V σ).decodeQuery pair.2 ∈
          (S.LD σ).accepting
            (Rounds.Role.layerBase R.params.rounds R.params.nl + 2)
            (Bcs.extend pref pair.1)
            (ms (Rounds.Role.layerBase R.params.rounds R.params.nl + 2))
            sys ((S.V σ).decodeChal pair.1)).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound) :
    ∀ pref : Fin (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) → C,
      ((univ.filter fun pair : C × C =>
        terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
          (S.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound := by
  classical
  intro pref
  let u := Rounds.Role.layerBase R.params.rounds R.params.nl + 1
  let ch := chain (nl := R.params.nl) (w := R.params.rounds)
    (S.V σ) (S.H σ) (S.asg σ) (S.Sat σ) (flatData (S.LD σ)) ms
  by_cases hb : ∃ sys : LigeroSystem ninp M F,
      ch.state u pref = .built sys ∧ Fits (S.V σ) sys ∧
        NoSat (S.asg σ) sys
  · obtain ⟨sys, hs, hf, hn⟩ := hb
    have hsubset :
        (univ.filter fun pair : C × C =>
          terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
            (S.LD σ) ms pref pair.1 pair.2) ⊆
        (univ.filter fun pair : C × C =>
          (S.V σ).decodeQuery pair.2 ∈
            (S.LD σ).accepting (u + 1) (Bcs.extend pref pair.1)
              (ms (u + 1)) sys ((S.V σ).decodeChal pair.1)) := by
      intro pair hp
      obtain ⟨sys', hs', _, _, hq⟩ :=
        (Finset.mem_filter.mp hp).2
      have heq : sys' = sys := by
        rw [hs] at hs'
        injection hs' with heq'
        exact heq'.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using hq⟩
    have hcard := Finset.card_le_card hsubset
    have hC : (0 : ℚ) < (Fintype.card C : ℚ) ^ 2 := by positivity
    have hqcard :
        (((univ.filter fun pair : C × C =>
          terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
            (S.LD σ) ms pref pair.1 pair.2).card : ℚ) /
            (Fintype.card C : ℚ) ^ 2) ≤
        (((univ.filter fun pair : C × C =>
          (S.V σ).decodeQuery pair.2 ∈
            (S.LD σ).accepting (u + 1) (Bcs.extend pref pair.1)
              (ms (u + 1)) sys ((S.V σ).decodeChal pair.1)).card : ℚ) /
            (Fintype.card C : ℚ) ^ 2) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (le_of_lt hC)
    exact hqcard.trans (hbuilt pref sys hs hf hn)
  · have hempty :
        (univ.filter fun pair : C × C =>
          terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
            (S.LD σ) ms pref pair.1 pair.2) = ∅ := by
      ext pair
      have hnot : ¬ terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
          (S.LD σ) ms pref pair.1 pair.2 := by
        intro hp
        obtain ⟨sys, hs, hf, hn, _⟩ := hp
        exact hb ⟨sys, hs, hf, hn⟩
      simp [hnot]
    rw [hempty]
    simpa using htermNonneg

/-- A fixed side's accepted paths have the certified field density plus any
response-uniform flat bound supplied for the final challenge/query pair. -/
theorem ZkSide.accepted_ratio_le_field_plus_terminal_density
    (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)
    (hF : Fintype.card F = R.params.row.fieldSize)
    (σ : Sig) (ms : ℕ → Msg)
    (hfalse : ∀ ℓ : S.Lift σ, ¬ S.Sat σ ℓ)
    (terminalBound : ℚ)
    (hterminal : ∀ pref : Fin
      (Rounds.Role.layerBase R.params.rounds R.params.nl + 1) → C,
      ((univ.filter fun pair : C × C =>
        terminalPairAccept (H := S.H σ) (Sat := S.Sat σ)
          (S.LD σ) ms pref pair.1 pair.2).card : ℚ) /
          (Fintype.card C : ℚ) ^ 2 ≤ terminalBound) :
    ((univ.filter fun tape : Fin
      (Rounds.Role.length R.params.nl R.params.rounds) → C =>
        ZkLayerStepAccepts .accepted .start
          (steps (nl := R.params.nl) (w := R.params.rounds)
            (S.V σ) (S.LD σ) ms) tape).card : ℚ) /
      (Fintype.card C : ℚ) ^
        Rounds.Role.length R.params.nl R.params.rounds ≤
      (R.cardCand : ℚ) * zkFieldDensity R logv + terminalBound := by
  exact accepted_ratio_le_field_plus_terminal (S.LD σ) ms hfalse
    ((R.cardCand : ℚ) * zkFieldDensity R logv) terminalBound
    (ZkSide.fieldPrefixEscape_ratio_le_density S hF σ ms) hterminal

end Lfzk.RbrZkFlat
