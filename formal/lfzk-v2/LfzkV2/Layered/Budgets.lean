import LfzkV2.Layered.FiatShamir
import LfzkV2.Packed.FrontendSizes

/-! The frontend pays the existing ordinary budget plus two nonzero roots
per layer. The new terminal never inherits the full-field denominator. -/

namespace LfzkV2.Layered.Replay

open SumcheckV2 Linear.Challenges
open LfzkV2.Replay (vectorSlots)

variable {F : Type}

theorem layerBudget_sum (fieldFiber nonzeroFiber : ℕ) {out input : ℕ}
    (circuit : Layered.Circuit F out input) :
    (∑ i : Fin (layerSlots circuit),
      (LayerRole.kind circuit ((layerRoleEquiv circuit).symm i)).rawBudget fieldFiber nonzeroFiber) =
      fieldFiber * circuit.ordinaryBudget + nonzeroFiber * (2 * circuit.layers) := by
  induction circuit with
  | input => simp [layerSlots, Layered.Circuit.ordinaryBudget, Layered.Circuit.layers]
  | entry n e rest ih =>
      let f := (finSumFinEquiv : Fin (vectorSlots n) ⊕ Fin (layerSlots rest) ≃ Fin (layerSlots (.entry n e rest)))
      let g := (Equiv.refl (Fin (vectorSlots n))).sumCongr (layerRoleEquiv rest)
      let k := fun role => (LayerRole.kind (.entry n e rest) (g.symm role)).rawBudget fieldFiber nonzeroFiber
      have hk role : (LayerRole.kind (.entry n e rest)
          ((layerRoleEquiv (.entry n e rest)).symm (f role))).rawBudget fieldFiber nonzeroFiber = k role :=
        congrArg k (f.symm_apply_apply role)
      have he := (f.sum_comp (fun i => (LayerRole.kind (.entry n e rest)
        ((layerRoleEquiv (.entry n e rest)).symm i)).rawBudget fieldFiber nonzeroFiber)).symm
      refine he.trans ((Finset.sum_congr rfl (fun role _ => hk role)).trans ?_)
      simp [k, g, Fintype.sum_sum_type, LayerRole.kind, Kind.rawBudget,
        ChallengeBlocks.Kind.budget, Layered.Circuit.ordinaryBudget, Layered.Circuit.layers]
      have hn : vectorSlots n * min 1 n = min 1 n := by cases n <;> simp [vectorSlots]
      simp only [Kind.rawBudget, ChallengeBlocks.Kind.budget] at ih
      nlinarith [congrArg (fun x => fieldFiber * x) hn]
  | @layer out mid input a body rest ih =>
      let e := (Equiv.refl (Fin (vectorSlots a))).sumCongr
        ((Equiv.refl (Fin mid)).sumCongr ((Equiv.refl (Fin 1)).sumCongr
          ((Equiv.refl (Fin 1)).sumCongr (layerRoleEquiv rest))))
      let k := fun role => (LayerRole.kind (.layer a body rest) (e.symm role)).rawBudget fieldFiber nonzeroFiber
      let f : (Fin (vectorSlots a) ⊕ Fin mid ⊕ Fin 1 ⊕ Fin 1 ⊕ Fin (layerSlots rest)) ≃
          Fin (layerSlots (.layer a body rest)) := (fiveSumEquiv (vectorSlots a) mid 1 1 (layerSlots rest)).trans
        (finCongr (by simp only [layerSlots]))
      have hk role : (LayerRole.kind (.layer a body rest)
          ((layerRoleEquiv (.layer a body rest)).symm (f role))).rawBudget fieldFiber nonzeroFiber = k role :=
        congrArg k (f.symm_apply_apply role)
      have ha : vectorSlots a * min 1 a = min 1 a := by
        cases a <;> simp [vectorSlots]
      have he := (f.sum_comp (fun i => (LayerRole.kind (.layer a body rest)
        ((layerRoleEquiv (.layer a body rest)).symm i)).rawBudget fieldFiber nonzeroFiber)).symm
      refine he.trans ((Finset.sum_congr rfl (fun role _ => hk role)).trans ?_)
      simp [k, e, Fintype.sum_sum_type, LayerRole.kind, Kind.rawBudget,
        ChallengeBlocks.Kind.budget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        mul_one, one_mul, Layered.Circuit.ordinaryBudget, Layered.Circuit.layers]
      simp only [Kind.rawBudget, ChallengeBlocks.Kind.budget] at ih
      nlinarith [congrArg (fun n => fieldFiber * n) ha]

theorem budget_sum (fieldFiber nonzeroFiber : ℕ) {out input : ℕ}
    (circuit : Layered.Circuit F out input) :
    (∑ i : Fin (slots circuit),
      (roleKind circuit ((roleEquiv circuit).symm i)).rawBudget fieldFiber nonzeroFiber) =
      fieldFiber * circuit.ordinaryBudget + nonzeroFiber * (2 * circuit.layers) :=
  layerBudget_sum fieldFiber nonzeroFiber circuit

theorem layerRole_budget_le (fieldFiber nonzeroFiber : ℕ) {out input : ℕ}
    (circuit : Layered.Circuit F out input) (role : LayerRole circuit) :
    (LayerRole.kind circuit role).rawBudget fieldFiber nonzeroFiber ≤
      max (fieldFiber * 2) (nonzeroFiber * 2) := by
  induction circuit with
  | input => exact Fin.elim0 role
  | entry n e rest ih =>
      cases role with
      | inl _ =>
          exact (Nat.mul_le_mul_left fieldFiber ((Nat.min_le_left 1 n).trans (by omega : 1 ≤ 2))).trans
            (le_max_left _ _)
      | inr role => exact ih role
  | layer a body rest ih =>
      rcases role with i | i | i | i | role
      · exact (Nat.mul_le_mul_left fieldFiber ((Nat.min_le_left 1 a).trans (by omega))).trans
          (le_max_left _ _)
      · exact le_max_left _ _
      · exact le_max_right _ _
      · exact (Nat.mul_le_mul_left fieldFiber (by omega : 1 ≤ 2)).trans (le_max_left _ _)
      · exact ih role

theorem roleKind_budget_le (fieldFiber nonzeroFiber : ℕ) {out input : ℕ}
    (circuit : Layered.Circuit F out input) (role : Role circuit) :
    (roleKind circuit role).rawBudget fieldFiber nonzeroFiber ≤
      max (fieldFiber * 2) (nonzeroFiber * 2) :=
  layerRole_budget_le fieldFiber nonzeroFiber circuit role

theorem pointKind_budget_le {Key : Type} (fieldFiber nonzeroFiber : ℕ) {out input : ℕ}
    (circuit : Layered.Circuit F out input) (point : Point Key F circuit) :
    (pointKind circuit point).rawBudget fieldFiber nonzeroFiber ≤
      max (fieldFiber * 2) (nonzeroFiber * 2) := by
  rcases point with ⟨key, opt⟩
  cases opt with
  | none => simp [pointKind, Kind.rawBudget, ChallengeBlocks.Kind.budget]
  | some p => exact roleKind_budget_le fieldFiber nonzeroFiber circuit _

end LfzkV2.Layered.Replay
