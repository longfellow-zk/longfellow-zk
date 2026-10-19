import Bcs.StoppedCharges
import Bcs.PairCompletion

/-! Stopped parent/query charges with a jointly completed verifier pair.
The extra premise is a fresh joint event bound, not a consumption bound
over adaptive commitments. -/
namespace Bcs.StoppedCharges
open Finset AffineBlock TotalOracle TotalOracle.Footprint StoppedPotential
open scoped Classical
variable {P R Q C : Type} [Fintype P] [Fintype R]
  [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

/-- Strengthen `(2*rate,rate)` to `(rate,rate)` when the selected pair's
fresh joint bad-event probability is also at most `rate`. -/
theorem oracle_sound_joint
    (embed : P ⊕ (P × R) ↪ Q) (domain : Finset Q)
    (hdom : ∀ x, embed x ∈ domain)
    (capacity : P → C → ℚ) (bad : P → R → C → C → Prop)
    (rate : ℚ) (hr : 0 ≤ rate) (hc : ∀ p a, 0 ≤ capacity p a)
    (hroot : ∀ p, average (fun a => repeatPrice rate (capacity p a)) ≤ rate)
    (hchild : ∀ p r a, average (fun b => indicator (bad p r a b)) ≤ capacity p a)
    (hjoint : ∀ p r, average (fun a => average (fun b => indicator (bad p r a b))) ≤ rate) :
    OracleSound domain
      (fun out H => bad out.1 out.2 (H (embed (.inl out.1))) (H (embed (.inr out))))
      (Rate.diagonal rate hr) := by
  classical
  have hcard : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  apply oracle_sound_of_embedded_pair_completion embed domain hdom
    (fun out : P × R => .inl out.1) (fun out => .inr out)
    (fun _ => Sum.inl_ne_inr) (weight embed capacity bad rate) ?_ ?_ rate hr ?_
    (fun out => bad out.1 out.2) (fun out => hjoint out.1 out.2) ?_
  · intro x H H' hoff c
    cases x with
    | inl p => rfl
    | inr pr =>
      have hn : embed (.inl pr.1) ≠ embed (.inr pr) := by
        intro h
        have he := embed.injective h
        cases he
      simp only [weight, hoff _ hn]
  · intro x H c
    cases x with
    | inl p => exact repeatPrice_nonneg _ _
    | inr pr =>
      exact mul_nonneg (sub_nonneg.mpr (repeatPrice_le_one _ _ hr (hc _ _)))
        (indicator_nonneg _)
  · intro x H
    cases x with
    | inl p =>
      simpa only [weight, mul_comm] using (div_le_iff₀ hcard).mp (hroot p)
    | inr pr =>
      let a := H (embed (.inl pr.1))
      let v := repeatPrice rate (capacity pr.1 a)
      have hv : 0 ≤ 1-v := sub_nonneg.mpr (repeatPrice_le_one _ _ hr (hc _ _))
      have he := (div_le_iff₀ hcard).mp (hchild pr.1 pr.2 a)
      have hp := (repeat_child_step_iff _ _ _).mp
        (repeatPrice_child_step (capacity pr.1 a) rate (hc _ _) hr)
      change (∑ b : C, (1-v) * indicator (bad pr.1 pr.2 a b)) ≤ Fintype.card C * rate
      rw [← mul_sum]
      calc
        _ ≤ (1-v) * (capacity pr.1 a * Fintype.card C) := mul_le_mul_of_nonneg_left he hv
        _ = Fintype.card C * (capacity pr.1 a * (1-v)) := by ring
        _ ≤ Fintype.card C * rate := mul_le_mul_of_nonneg_left hp hcard.le
  · intro out H hb
    change 1 ≤ repeatPrice rate (capacity out.1 (H (embed (.inl out.1)))) +
      (1-repeatPrice rate (capacity out.1 (H (embed (.inl out.1))))) *
        indicator (bad out.1 out.2 (H (embed (.inl out.1))) (H (embed (.inr out))))
    simp only [indicator, if_pos hb, mul_one]
    linarith

end Bcs.StoppedCharges
