import Bcs.StoppedPotential
import Bcs.AffinePotential

/-! Static stopped-price charges. The parent and child coordinates are
charged separately, so their order in an adaptive oracle execution is
irrelevant. A uniform conditional-capacity majorant is essential. -/
namespace Bcs.StoppedCharges
open Finset AffineBlock TotalOracle TotalOracle.Footprint StoppedPotential
open scoped Classical

theorem repeatPrice_le_one (rate capacity : ℚ) (hr : 0 ≤ rate) (hc : 0 ≤ capacity) :
    repeatPrice rate capacity ≤ 1 := by
  by_cases hz : capacity = 0
  · simp [repeatPrice, hz]
  · simp only [repeatPrice, if_neg hz]
    apply max_le (by norm_num)
    linarith [div_nonneg hr hc]

noncomputable def indicator (E : Prop) : ℚ := if E then 1 else 0

theorem indicator_nonneg (E : Prop) : 0 ≤ indicator E := by
  unfold indicator
  split_ifs <;> norm_num

variable {P R Q C : Type} [Fintype P] [Fintype R]
  [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

def point (out : P × R) (i : ℕ) : P ⊕ (P × R) :=
  if i = 0 then .inl out.1 else .inr out

omit [Fintype P] [Fintype R] in
private theorem point_injective (out : P × R) :
    Function.Injective (fun i : Fin 2 => point out i.val) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [point]

noncomputable def weight (embed : P ⊕ (P × R) ↪ Q)
    (capacity : P → C → ℚ) (bad : P → R → C → C → Prop) (rate : ℚ) :
    P ⊕ (P × R) → (Q → C) → C → ℚ
  | .inl p, _, a => repeatPrice rate (capacity p a)
  | .inr (p,r), H, b =>
    (1-repeatPrice rate (capacity p (H (embed (.inl p))))) *
      indicator (bad p r (H (embed (.inl p))) b)

/-- A genuine local-domain OracleSound certificate from stopped prices.
The majorant is uniform in the child commitment r. No query-order or
limit on the number of child commitments is assumed. The two verifier
lookups give intercept 2*rate; prover queries pay rate. -/
theorem oracle_sound
    (embed : P ⊕ (P × R) ↪ Q) (domain : Finset Q)
    (hdom : ∀ x, embed x ∈ domain)
    (capacity : P → C → ℚ) (bad : P → R → C → C → Prop)
    (rate : ℚ) (hr : 0 ≤ rate) (hc : ∀ p a, 0 ≤ capacity p a)
    (hroot : ∀ p, average (fun a => repeatPrice rate (capacity p a)) ≤ rate)
    (hchild : ∀ p r a, average (fun b => indicator (bad p r a b)) ≤ capacity p a) :
    OracleSound domain
      (fun out H => bad out.1 out.2 (H (embed (.inl out.1))) (H (embed (.inr out))))
      ⟨2*rate, rate, by positivity, hr⟩ := by
  let card : ℚ := Fintype.card C
  have hcard : 0 < card := by dsimp [card]; exact_mod_cast Fintype.card_pos
  let budget : P ⊕ (P × R) → ℚ := fun _ => card * rate
  let slots : Fin 2 → ℚ := fun _ => card * rate
  apply oracle_sound_of_embedded_charges embed domain point point_injective
    (weight embed capacity bad rate) ?_ ?_ budget ?_ ?_
    ⟨2*rate, rate, by positivity, hr⟩ slots ?_ ?_ ?_ _ ?_
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
  · intro x; dsimp [budget]; positivity
  · intro x H
    cases x with
    | inl p =>
      simpa only [weight, budget, mul_comm] using (div_le_iff₀ hcard).mp (hroot p)
    | inr pr =>
      let a := H (embed (.inl pr.1))
      let v := repeatPrice rate (capacity pr.1 a)
      have hv : 0 ≤ 1-v := sub_nonneg.mpr (repeatPrice_le_one _ _ hr (hc _ _))
      have he := (div_le_iff₀ hcard).mp (hchild pr.1 pr.2 a)
      have hp := (repeat_child_step_iff _ _ _).mp
        (repeatPrice_child_step (capacity pr.1 a) rate (hc _ _) hr)
      change (∑ b : C, (1-v) * indicator (bad pr.1 pr.2 a b)) ≤ card * rate
      rw [← mul_sum]
      calc
        _ ≤ (1-v) * (capacity pr.1 a * card) := mul_le_mul_of_nonneg_left he hv
        _ = card * (capacity pr.1 a * (1-v)) := by ring
        _ ≤ card * rate := mul_le_mul_of_nonneg_left hp hcard.le
  · intro x
    simp only [budget, hdom x, if_true]
    rfl
  · intro out i; rfl
  · change (∑ _i : Fin 2, card * rate) ≤ card * (2*rate)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num only [Nat.cast_ofNat]
    ring_nf
    rfl
  · intro out H hbad
    change (1 : ℚ) ≤ ∑ i : Fin 2,
      weight embed capacity bad rate (point out i.val) H (H (embed (point out i.val)))
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    change (1 : ℚ) ≤ repeatPrice rate (capacity out.1 (H (embed (.inl out.1)))) +
      ((1-repeatPrice rate (capacity out.1 (H (embed (.inl out.1)))))*
        indicator (bad out.1 out.2 (H (embed (.inl out.1))) (H (embed (.inr out)))) + 0)
    simp only [indicator, if_pos hbad, mul_one, add_zero]
    linarith

end Bcs.StoppedCharges
